defmodule ShotUnifyTest do
  use ExUnit.Case
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl
  import ShotDs.Stt.Numerals
  alias ShotDs.Data.{Declaration, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUnify.UnifSolution

  @moduletag timeout: 1000

  setup do
    reset_term_pool()
    :ok
  end

  test "returns no solutions when depth is zero" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())

    assert [] == Enum.to_list(ShotUnify.unify({x, y}, 0))
  end

  test "returns one empty solution for empty problems" do
    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUnify.unify([], 3))
  end

  test "drops trivial equal pairs" do
    a = TF.make_const_term("a", type_i())

    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUnify.unify({a, a}, 3))
  end

  test "fails for incompatible term types" do
    a = TF.make_const_term("a", type_i())
    t = true_term()

    assert [] == Enum.to_list(ShotUnify.unify({a, t}, 3))
  end

  test "fails for incompatible rigid heads" do
    a = TF.make_const_term("a", type_i())
    b = TF.make_const_term("b", type_i())

    assert [] == Enum.to_list(ShotUnify.unify({a, b}, 3))
  end

  test "keeps flex-flex pairs in the solution" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())

    assert [%UnifSolution{substitutions: [], flex_pairs: [{^x, ^y}]}] =
             Enum.to_list(ShotUnify.unify({x, y}, 3))
  end

  test "binds a free variable to a rigid term" do
    x = TF.make_free_var_term("X", type_i())
    a = TF.make_const_term("a", type_i())

    [solution] = Enum.to_list(ShotUnify.unify({x, a}, 3))

    assert %UnifSolution{substitutions: [subst], flex_pairs: []} = solution
    assert subst.fvar.kind == :fv
    assert subst.fvar.name == "X"
    assert subst.term_id == a
  end

  test "enforces occurs-check for direct bindings" do
    x = TF.make_free_var_term("X", type_i())
    x_head = TF.get_term(x).head

    right =
      TF.memoize(%Term{
        id: 0,
        head: Declaration.new_const("c", type_i()),
        args: [],
        bvars: [],
        type: type_i(),
        fvars: [x_head],
        max_num: 0
      })

    assert [] == Enum.to_list(ShotUnify.unify({x, right}, 3))
  end

  test "migrates old flex pairs back into the work list after substitution" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())
    a = TF.make_const_term("a", type_i())

    solutions = Enum.to_list(ShotUnify.unify([{x, y}, {x, a}], 5))

    assert Enum.any?(solutions, fn %UnifSolution{substitutions: substs, flex_pairs: []} ->
             Enum.any?(substs, &(&1.fvar.name == "X" and &1.term_id == a)) and
               Enum.any?(substs, &(&1.fvar.name == "Y" and &1.term_id == a))
           end)
  end

  test "decomposes compatible rigid bound heads" do
    t1 = mk_bv_term(1, 3, type_i())
    t2 = mk_bv_term(2, 4, type_i())

    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUnify.unify({t1, t2}, 3))
  end

  test "fails for incompatible rigid bound heads" do
    t1 = mk_bv_term(1, 3, type_i())
    t2 = mk_bv_term(1, 4, type_i())

    assert [] == Enum.to_list(ShotUnify.unify({t1, t2}, 3))
  end

  test "creates branches for non-trivial flex-rigid problems" do
    x = TF.make_const_term("x", type_i())
    fx = mk_flex_appl_term("F", Type.new(:i, :i), x, type_i())
    c = TF.make_const_term("c", type_i())

    assert [_ | _] = Enum.to_list(ShotUnify.unify({fx, c}, 3))
  end

  test "solves Church numeral multiplication variable for X" do
    x_times_5 = mult(num_var("X"), num(5))
    target = num(30)

    [solution] = Enum.to_list(ShotUnify.unify({x_times_5, target}))

    assert %UnifSolution{substitutions: [subst], flex_pairs: []} = solution
    assert subst.fvar.name == "X"
    assert subst.term_id == num(6)
  end

  test "creates branches for non-trivial rigid-flex problems" do
    x = TF.make_const_term("x", type_i())
    fx = mk_flex_appl_term("F", Type.new(:i, :i), x, type_i())
    c = TF.make_const_term("c", type_i())

    assert [_ | _] = Enum.to_list(ShotUnify.unify({c, fx}, 3))
  end

  test "creates projection branches for non-trivial flex-bound problems" do
    x = TF.make_const_term("x", type_i())
    fx = mk_flex_appl_term("F", Type.new(:i, :i), x, type_i())
    b = mk_bv_term(1, 1, type_i())

    assert is_list(Enum.to_list(ShotUnify.unify({fx, b}, 3)))
  end

  test "creates projection branches for non-trivial bound-flex problems" do
    x = TF.make_const_term("x", type_i())
    fx = mk_flex_appl_term("F", Type.new(:i, :i), x, type_i())
    b = mk_bv_term(1, 1, type_i())

    assert is_list(Enum.to_list(ShotUnify.unify({b, fx}, 3)))
  end

  test "binds a rigid term to a free variable on the right" do
    x = TF.make_free_var_term("X", type_i())
    a = TF.make_const_term("a", type_i())

    [solution] = Enum.to_list(ShotUnify.unify({a, x}, 3))

    assert Enum.any?(solution.substitutions, &(&1.fvar.name == "X" and &1.term_id == a))
  end

  test "keeps unaffected flex pairs during substitution updates" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())
    z = TF.make_free_var_term("Z", type_i())
    a = TF.make_const_term("a", type_i())

    solutions = Enum.to_list(ShotUnify.unify([{x, y}, {z, a}], 5))

    assert Enum.any?(solutions, fn %UnifSolution{substitutions: substs, flex_pairs: flex} ->
             Enum.any?(substs, &(&1.fvar.name == "Z" and &1.term_id == a)) and
               Enum.any?(flex, fn {l, r} -> l == x and r == y end)
           end)
  end

  test "decomposes rigid constants with aligned argument lists" do
    a = TF.make_const_term("a", type_i())
    b = TF.make_const_term("b", type_i())
    c = Declaration.new_const("h", Type.new(:i, [:i, :i]))

    t1 =
      TF.memoize(%Term{
        id: 0,
        head: c,
        args: [a, b],
        bvars: [],
        type: type_i(),
        fvars: [],
        max_num: 0
      })

    t2 =
      TF.memoize(%Term{
        id: 0,
        head: c,
        args: [a, b],
        bvars: [],
        type: type_i(),
        fvars: [],
        max_num: 0
      })

    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUnify.unify({t1, t2}, 3))
  end

  test "raises when rigid decomposition sees different arities" do
    a = TF.make_const_term("a", type_i())
    c = Declaration.new_const("h", Type.new(:i, [:i, :i]))

    t1 =
      TF.memoize(%Term{
        id: 0,
        head: c,
        args: [a],
        bvars: [],
        type: type_i(),
        fvars: [],
        max_num: 0
      })

    t2 =
      TF.memoize(%Term{
        id: 0,
        head: c,
        args: [a, a],
        bvars: [],
        type: type_i(),
        fvars: [],
        max_num: 0
      })

    assert_raise RuntimeError, ~r/ArgumentError: can only decompose terms/, fn ->
      Enum.to_list(ShotUnify.unify({t1, t2}, 3))
    end
  end

  test "tuple and list input forms behave the same" do
    x = TF.make_free_var_term("X", type_i())
    a = TF.make_const_term("a", type_i())

    tuple_solutions = Enum.to_list(ShotUnify.unify({x, a}, 3))
    list_solutions = Enum.to_list(ShotUnify.unify([{x, a}], 3))

    assert Enum.map(tuple_solutions, &Kernel.to_string/1) ==
             Enum.map(list_solutions, &Kernel.to_string/1)
  end

  test "Imitation generates helper variables which are correctly cleaned up" do
    a = TF.make_const_term("a", type_i())
    c = TF.make_const_term("c", type_ii())
    f_var = TF.make_free_var_term("F", type_ii())

    t1 = app(f_var, a)
    t2 = app(c, a)

    solutions = ShotUnify.unify({t1, t2}) |> Enum.to_list()

    assert not Enum.empty?(solutions), "Should find at least one solution"

    Enum.each(solutions, fn sol ->
      assert length(sol.substitutions) == 1,
             "Expected exactly 1 substitution (for F), but got #{length(sol.substitutions)}. Leak detected!"

      subst = hd(sol.substitutions)

      assert subst.fvar.name == "F",
             "The remaining substitution should be for the initial user variable F"
    end)
  end

  test "Higher-Order Projection correctly resolves transitive dependencies" do
    a = TF.make_const_term("a", type_i())
    g = TF.make_const_term("g", type_ii())
    f_var = TF.make_free_var_term("F", Type.new(:i, type_ii()))

    t1 = app(f_var, g)
    t2 = app(g, a)

    solutions = ShotUnify.unify({t1, t2}) |> Enum.to_list()

    assert not Enum.empty?(solutions)

    valid_projection_found =
      Enum.any?(solutions, fn sol ->
        if length(sol.substitutions) != 1, do: false, else: true

        subst = hd(sol.substitutions)
        normalized_term = TF.get_term(subst.term_id)

        Enum.empty?(normalized_term.fvars) and subst.fvar.name == "F"
      end)

    assert valid_projection_found,
           "Expected a cleanly normalized substitution for F with no dangling helper variables."
  end

  defp mk_bv_term(name, max_num, type) do
    bv = Declaration.new_bound_var(name, type)

    TF.memoize(%Term{
      id: 0,
      head: bv,
      args: [],
      bvars: [],
      type: type,
      fvars: [],
      max_num: max_num
    })
  end

  defp mk_flex_appl_term(name, head_type, arg_id, result_type) do
    head = Declaration.new_free_var(name, head_type)
    arg_term = TF.get_term(arg_id)

    TF.memoize(%Term{
      id: 0,
      head: head,
      args: [arg_id],
      bvars: [],
      type: result_type,
      fvars: Enum.uniq([head | arg_term.fvars]),
      max_num: arg_term.max_num
    })
  end

  defp reset_term_pool do
    case :ets.whereis(:term_pool) do
      :undefined ->
        :ok

      _ ->
        :ets.delete_all_objects(:term_pool)
        :ets.insert(:term_pool, {:id_counter, 0})
    end
  end
end
