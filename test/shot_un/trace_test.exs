defmodule ShotUn.TraceTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.Trace
  alias ShotUn.Trace.{Mermaid, Node}
  alias ShotUn.UnifSolution

  describe "ShotUn.unify with vis: true (pre-unification)" do
    test "returns {stream, trace} and the stream is materialised" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      {stream, %Trace{} = trace} = ShotUn.unify({x, c}, 10, vis: true)

      assert [%UnifSolution{} | _] = Enum.to_list(stream)
      assert trace.algorithm == :pre_unification
      assert %Node{kind: :start, rule: :init} = trace.root
    end

    test "trace records the bind transition to a solution leaf" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      {_stream, trace} = ShotUn.unify({x, c}, 10, vis: true)

      [bind_node] = trace.root.children
      assert bind_node.rule == :bind
      assert bind_node.kind == :step

      [sol_node] = bind_node.children
      assert sol_node.kind == :solution
      assert sol_node.rule == :solved
      assert sol_node.children == []
    end

    test "trace branches for flex-rigid imitation+projection" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())

      {_stream, trace} =
        ShotUn.unify({app(x, [a, a]), app(f, [a, a])}, 10, vis: true)

      # Top-level projections substitute `a =? f(a,a)` and fail; they're
      # pruned. The lone surviving child is the imitation; under it, the
      # H_i subgoals each branch into imitation+projection again.
      all_rules = collect_rules(trace.root)
      assert :imitation in all_rules
      assert :projection in all_rules
      assert Enum.all?(trace.root.children, &has_solution_leaf?/1)
    end

    test "trace is empty (just root) when no solution exists within depth" do
      a = TF.make_const_term("a", type_i())
      b = TF.make_const_term("b", type_i())

      {stream, trace} = ShotUn.unify({a, b}, 5, vis: true)

      assert [] == Enum.to_list(stream)
      assert trace.root.kind == :start
      # rigid_clash failure was pruned out — only the root remains.
      assert trace.root.children == []
    end

    test "vis: false keeps the original Stream return shape" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      result = ShotUn.unify({x, c}, 10)

      refute is_tuple(result)
      assert [%UnifSolution{}] = Enum.to_list(result)
    end
  end

  describe "ShotUn.match with vis: true" do
    test "returns {stream, trace} for second-order matching" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())

      {stream, trace} = ShotUn.match({app(x, [a, a]), app(f, [a, a])}, vis: true)

      sols = Enum.to_list(stream)
      assert length(sols) == 9
      assert trace.algorithm == :matching
      assert trace.root.kind == :start
      # Every direct child of the root must lead to a solution after pruning.
      assert Enum.all?(trace.root.children, &has_solution_leaf?/1)
    end
  end

  describe "ShotUn.pattern_unify with vis: true" do
    test "returns {result, trace} with a linear chain for a pattern problem" do
      x = TF.make_free_var_term("X", type_i())
      y = TF.make_free_var_term("Y", type_i())

      {{:ok, %UnifSolution{flex_pairs: []}}, trace} =
        ShotUn.pattern_unify({x, y}, vis: true)

      assert trace.algorithm == :pattern
      assert trace.root.kind == :start
      assert trace.root.children != []
      assert has_solution_leaf?(trace.root)
    end

    test "trace is just the root when no MGU exists" do
      a = TF.make_const_term("a", type_i())
      b = TF.make_const_term("b", type_i())

      {:error, trace} = ShotUn.pattern_unify({a, b}, vis: true)

      assert trace.root.children == []
    end
  end

  describe "Trace.prune_to_solutions/1" do
    test "drops failure leaves while preserving the root" do
      fail = %Node{id: 2, parent_id: 1, kind: :fail, rule: :type_mismatch, children: []}
      sol = %Node{id: 1, parent_id: 0, kind: :solution, rule: :solved, children: []}
      root = %Node{id: 0, parent_id: nil, kind: :start, rule: :init, children: [sol, fail]}
      trace = %Trace{root: root}

      pruned = Trace.prune_to_solutions(trace)

      assert pruned.root.id == 0
      assert [%Node{kind: :solution}] = pruned.root.children
    end

    test "drops intermediate steps that don't lead to a solution" do
      dead_step =
        %Node{
          id: 3,
          parent_id: 1,
          kind: :step,
          rule: :bind,
          children: [%Node{id: 4, parent_id: 3, kind: :fail, rule: :occurs, children: []}]
        }

      sol_step =
        %Node{
          id: 2,
          parent_id: 1,
          kind: :step,
          rule: :bind,
          children: [%Node{id: 5, parent_id: 2, kind: :solution, rule: :solved, children: []}]
        }

      root =
        %Node{
          id: 0,
          parent_id: nil,
          kind: :start,
          rule: :init,
          children: [sol_step, dead_step]
        }

      pruned = Trace.prune_to_solutions(%Trace{root: root})

      assert [%Node{id: 2, children: [%Node{kind: :solution}]}] = pruned.root.children
    end
  end

  describe "concurrent vis: true calls" do
    test "two processes calling unify simultaneously each get their own trace" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())
      pair = {app(x, [a, a]), app(f, [a, a])}

      pid = self()

      tasks =
        for i <- 1..4 do
          Task.async(fn ->
            {stream, trace} = ShotUn.unify(pair, 10, vis: true)
            send(pid, {:trace, i, length(Enum.to_list(stream)), trace})
            trace
          end)
        end

      results = Enum.map(tasks, &Task.await/1)

      # Every concurrent call must produce a fully-populated trace tree.
      assert length(results) == 4

      Enum.each(results, fn trace ->
        assert %ShotUn.Trace{algorithm: :pre_unification} = trace
        assert trace.root.kind == :start
        # Each branch must reach a solution (9 total in the original 9-sols test).
        assert Enum.all?(trace.root.children, &has_solution_leaf?/1)
      end)

      # IDs in each trace start at 0 — they don't share a counter.
      Enum.each(results, fn trace -> assert trace.root.id == 0 end)
    end

    test "after unify with vis: true, the tracer is fully torn down" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      {_stream, _trace} = ShotUn.unify({x, c}, 10, vis: true)

      assert ShotUn.Tracer.current_table() == nil
      refute ShotUn.Tracer.active?()
    end
  end

  describe "ShotUn.Trace.Mermaid.render/2" do
    test "produces a graph TD diagram with classDefs and a solution node" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      {_stream, trace} = ShotUn.unify({x, c}, 10, vis: true)

      output = Mermaid.render(trace)

      assert output =~ "graph TD"
      assert output =~ "classDef start"
      assert output =~ "classDef solution"
      # Prose runs are split one word per `\text{…}` (to avoid nbsp in
      # KaTeX's MathML output), so the label carries the star and the
      # word in adjacent `\text{}` blocks.
      assert output =~ "\\text{★}\\;\\text{solution}"
      assert output =~ "-.->"
      assert output =~ "N0[\""
    end

    test "uses solid arrows for branching choice points" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())

      {_stream, trace} =
        ShotUn.unify({app(x, [a, a]), app(f, [a, a])}, 10, vis: true)

      output = Mermaid.render(trace)

      assert output =~ "==>"
      assert output =~ "imitation"
      assert output =~ "projection"
    end

    test "empty trace renders to empty string" do
      assert "" == Mermaid.render(%Trace{root: nil})
    end
  end

  defp has_solution_leaf?(%Node{kind: :solution}), do: true

  defp has_solution_leaf?(%Node{children: children}),
    do: Enum.any?(children, &has_solution_leaf?/1)

  defp collect_rules(%Node{rule: r, children: cs}) do
    [r | Enum.flat_map(cs, &collect_rules/1)]
  end
end
