defmodule ShotUnify do
  @moduledoc """
  Implements (syntactic) higher-order pre-unification for term pairs based on
  projection and imitation.
  """
  alias ShotDs.Data.Type
  alias ShotDs.Data.{Term, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics
  alias ShotUnify.UnifSolution
  alias ShotUnify.Bindings

  @typep term_pair :: {Term.term_id(), Term.term_id()}
  @typep search_state :: %{
           pairs: [term_pair()],
           subst: [Substitution.t()],
           flex: [term_pair()],
           depth: non_neg_integer()
         }
  @typep step_t ::
           :fail
           | {:solution, UnifSolution.t()}
           | {:branch, [search_state()]}
           | {:next, search_state()}

  @doc """
  Implements depth-bounded higher-order pre-unification to solve a unification
  problem consisting of a single term pair or a list of term pairs. Returns a
  lazy stream of unification solutions.
  """
  @spec unify([term_pair()] | term_pair(), non_neg_integer()) :: Enumerable.t(UnifSolution.t())
  def unify(term_pairs, depth \\ 10)

  def unify(term_pairs, depth) when is_list(term_pairs) do
    Stream.resource(
      fn ->
        TF.start_scratchpad()

        initial_scope =
          Enum.reduce(term_pairs, MapSet.new(), fn {l_id, r_id}, acc ->
            l_fvars = TF.get_term(l_id).fvars |> MapSet.new()
            r_fvars = TF.get_term(r_id).fvars |> MapSet.new()

            acc
            |> MapSet.union(l_fvars)
            |> MapSet.union(r_fvars)
          end)

        initial_state = %{pairs: term_pairs, substs: [], flex: [], depth: depth}

        {[initial_state], initial_scope}
      end,
      fn
        {[], _scope} = acc ->
          {:halt, acc}

        {[current | remaining], scope} = acc ->
          case explore_branch([current | remaining]) do
            nil ->
              {:halt, acc}

            {raw_solution, new_stack} ->
              cleaned_solution = clean_solution(raw_solution, scope)
              committed_solution = commit_solution(cleaned_solution)
              {[committed_solution], {new_stack, scope}}
          end
      end,
      fn _acc ->
        TF.stop_scratchpad()
      end
    )
  end

  def unify({t1, t2} = pair, depth) when is_integer(t1) and is_integer(t2),
    do: unify([pair], depth)

  defp clean_solution(%{substitutions: substs, flex_pairs: flex}, initial_scope) do
    normalized_substs =
      substs
      |> Enum.filter(&MapSet.member?(initial_scope, &1.fvar))
      |> Enum.map(&%{&1 | term_id: Semantics.subst(substs, &1.term_id)})

    normalized_flex =
      Enum.map(flex, fn {l_id, r_id} ->
        {Semantics.subst(substs, l_id), Semantics.subst(substs, r_id)}
      end)

    %UnifSolution{substitutions: normalized_substs, flex_pairs: normalized_flex}
  end

  defp commit_solution(%UnifSolution{substitutions: substs, flex_pairs: flex}) do
    committed_substs =
      Enum.map(substs, fn subst ->
        %{subst | term_id: TF.commit_to_global(subst.term_id)}
      end)

    committed_flex =
      Enum.map(flex, fn {l_id, r_id} ->
        {TF.commit_to_global(l_id), TF.commit_to_global(r_id)}
      end)

    %UnifSolution{substitutions: committed_substs, flex_pairs: committed_flex}
  end

  ##############################################################################
  # MAIN UNIFICATION LOGIC
  ##############################################################################

  @spec explore_branch([search_state()]) :: {UnifSolution.t(), [search_state()]} | nil
  defp explore_branch([]), do: nil

  defp explore_branch([current | remaining]) do
    case step(current) do
      :fail ->
        explore_branch(remaining)

      {:solution, solution} ->
        {solution, remaining}

      {:branch, new_branches} ->
        explore_branch(new_branches ++ remaining)

      {:next, updated_state} ->
        explore_branch([updated_state | remaining])
    end
  end

  @spec step(search_state()) :: step_t()
  defp step(%{depth: 0}), do: :fail

  defp step(%{pairs: [], substs: substs, flex: flex}),
    do: {:solution, %UnifSolution{substitutions: substs, flex_pairs: flex}}

  defp step(%{pairs: [{left_id, right_id} | rest]} = state) do
    # Trivial case
    if left_id == right_id do
      {:next, %{state | pairs: rest}}
    else
      left = TF.get_term(left_id)
      right = TF.get_term(right_id)

      evaluate_pair(left, right, state, rest)
    end
  end

  @spec evaluate_pair(Term.t(), Term.t(), search_state(), term_pair()) :: step_t()
  defp evaluate_pair(term_1, term_2, state, rest)

  # Case: incompatible types (we assume monotypes)
  defp evaluate_pair(%Term{type: t1}, %Term{type: t2}, _s, _r) when t1 != t2,
    do: :fail

  # Case: rigid-rigid (constants)
  defp evaluate_pair(
         %Term{head: %{kind: :co} = c} = left,
         %Term{head: %{kind: :co} = c} = right,
         state,
         rest
       ) do
    new_pairs = decompose(left, right)
    {:next, %{state | pairs: new_pairs ++ rest}}
  end

  # Case: rigid-rigid (bound variables)
  defp evaluate_pair(
         %Term{head: %{kind: :bv} = left_head} = left,
         %Term{head: %{kind: :bv} = right_head} = right,
         state,
         rest
       ) do
    if same_bound_slot?(left, left_head, right, right_head) do
      new_pairs = decompose(left, right)
      {:next, %{state | pairs: new_pairs ++ rest}}
    else
      :fail
    end
  end

  # Case: flex-flex
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs
    {:next, %{state | pairs: rest, flex: [{l_id, r_id} | state.flex]}}
  end

  # Case: bind left
  defp evaluate_pair(
         %Term{head: %{kind: :fv} = var, args: [], bvars: []},
         right,
         state,
         rest
       ),
       do: bind(var, right, state, rest)

  # Case: bind right
  defp evaluate_pair(
         left,
         %Term{head: %{kind: :fv} = var, args: [], bvars: []},
         state,
         rest
       ),
       do: bind(var, left, state, rest)

  # Case: flex-rigid
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :co}}, state, rest),
    do: do_bindings([:imitation, :projection, :prim_subst], state, rest)

  # Case: rigid-flex
  defp evaluate_pair(%Term{head: %{kind: :co}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs

    do_bindings(
      [:imitation, :projection, :prim_subst],
      %{state | pairs: [{r_id, l_id} | rest]},
      rest
    )
  end

  # Case: flex-bound
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :bv}}, state, rest),
    do: do_bindings([:projection], state, rest)

  # Case: Bound-flex
  defp evaluate_pair(%Term{head: %{kind: :bv}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs
    do_bindings([:projection], %{state | pairs: [{r_id, l_id} | rest]}, rest)
  end

  # Rest cases: incompatible rigid heads etc.
  defp evaluate_pair(_left, _right, _state, _rest), do: :fail

  ##############################################################################
  # FURTHER HELPERS
  ##############################################################################

  defp apply_substitution(new_subst, state, rest_pairs) do
    updated_substs = Semantics.add_subst(state.substs, new_subst)

    updated_pairs =
      Enum.map(rest_pairs, fn {l_id, r_id} ->
        {Semantics.subst(new_subst, l_id), Semantics.subst(new_subst, r_id)}
      end)

    {remaining_flex, migrated_pairs} =
      Enum.reduce(state.flex, {[], []}, fn {l_id, r_id}, {flex_acc, pairs_acc} ->
        new_l = Semantics.subst(new_subst, l_id)
        new_r = Semantics.subst(new_subst, r_id)

        l_head_kind = TF.get_term(new_l).head.kind
        r_head_kind = TF.get_term(new_r).head.kind

        if l_head_kind == :fv and r_head_kind == :fv do
          {[{new_l, new_r} | flex_acc], pairs_acc}
        else
          {flex_acc, [{new_l, new_r} | pairs_acc]}
        end
      end)

    %{
      state
      | substs: updated_substs,
        pairs: migrated_pairs ++ updated_pairs,
        flex: remaining_flex
    }
  end

  defp bind(var, right_term, state, rest_pairs) do
    if var in right_term.fvars do
      # variable capture
      :fail
    else
      new_subst = Substitution.new(var, right_term.id)
      {:next, apply_substitution(new_subst, state, rest_pairs)}
    end
  end

  defp decompose(%Term{bvars: l_bvars, args: l_args}, %Term{bvars: r_bvars, args: r_args}) do
    if length(l_args) != length(r_args) do
      raise "ArgumentError: can only decompose terms with the same amount of arguments."
    end

    l_wrapped = Enum.map(l_args, &wrap_in_bvars(&1, l_bvars))
    r_wrapped = Enum.map(r_args, &wrap_in_bvars(&1, r_bvars))

    Enum.zip(l_wrapped, r_wrapped)
  end

  defp wrap_in_bvars(term_id, []), do: term_id

  defp wrap_in_bvars(term_id, new_bvars) do
    %Term{type: original_type} = term = TF.get_term(term_id)

    combined_bvars = new_bvars ++ term.bvars

    bvar_maxes = Enum.map(combined_bvars, & &1.name)
    new_max_num = Enum.max([term.max_num | bvar_maxes], fn -> 0 end)

    new_bvar_types = Enum.map(new_bvars, & &1.type)
    new_type = Type.new(original_type, new_bvar_types)

    wrapped_term = %Term{term | bvars: combined_bvars, type: new_type, max_num: new_max_num}
    TF.memoize(wrapped_term)
  end

  # Generates imitation/projection/prim-subst branches and returns them as a
  # list of new states
  defp do_bindings(binding_types, state, rest_pairs) do
    [{flex_id, rigid_id} | _] = state.pairs

    flex_head = TF.get_term(flex_id).head
    rigid_head = TF.get_term(rigid_id).head

    standard_substs = Bindings.generic_binding(flex_head, rigid_head, binding_types)

    prim_substs =
      if :prim_subst in binding_types do
        Bindings.prim_subst_bindings(flex_head, rigid_head)
      else
        []
      end

    all_substitutions = standard_substs ++ prim_substs

    new_branches =
      Enum.map(all_substitutions, fn subst ->
        state
        |> then(&apply_substitution(subst, &1, [{flex_id, rigid_id} | rest_pairs]))
        |> Map.update!(:depth, &(&1 - 1))
      end)

    {:branch, new_branches}
  end

  defp same_bound_slot?(left_term, left_head, right_term, right_head) do
    left_slot = bound_slot(left_term, left_head)
    right_slot = bound_slot(right_term, right_head)

    not is_nil(left_slot) and left_slot == right_slot
  end

  defp bound_slot(%Term{bvars: bvars, max_num: max_num}, %{name: name, type: type}) do
    exact_index =
      Enum.find_index(bvars, fn bv ->
        bv.name == name and bv.type == type
      end)

    case exact_index do
      nil ->
        matching_by_type =
          bvars
          |> Enum.with_index()
          |> Enum.filter(fn {bv, _idx} -> bv.type == type end)

        case matching_by_type do
          [{_bv, idx}] -> idx
          _ -> max_num - name
        end

      _ ->
        exact_index
    end
  end
end
