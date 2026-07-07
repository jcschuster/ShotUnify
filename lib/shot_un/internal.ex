defmodule ShotUn.Internal do
  @moduledoc false
  # Shared helpers used by the pre-unification, matching and pattern
  # unification algorithms. State-agnostic: every function operates on
  # plain term IDs and returns plain term IDs or new pairs.

  alias ShotDs.Data.{Declaration, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF

  @typep term_pair :: {Term.term_id(), Term.term_id()}

  @doc """
  Decomposes a rigid-rigid pair of terms with matching head shapes into a
  list of new pairs by zipping their argument lists, wrapping each argument
  in the parent term's lambda binders so the resulting pairs are well-typed
  at the top level.
  """
  @spec decompose(Term.t(), Term.t()) :: {:ok, [term_pair()]} | :error
  def decompose(%Term{bvars: l_bvars, args: l_args}, %Term{bvars: r_bvars, args: r_args}) do
    if length(l_args) != length(r_args) do
      :error
    else
      l_wrapped = Enum.map(l_args, &wrap_in_bvars(&1, l_bvars))
      r_wrapped = Enum.map(r_args, &wrap_in_bvars(&1, r_bvars))
      {:ok, Enum.zip(l_wrapped, r_wrapped)}
    end
  end

  @doc """
  Wraps the given term in additional outer lambda binders, prepending them
  to the term's existing `:bvars` field. Returns the original term ID when
  no new binders are needed.
  """
  @spec wrap_in_bvars(Term.term_id(), [Declaration.bound_var_t()]) :: Term.term_id()
  def wrap_in_bvars(term_id, []), do: term_id

  def wrap_in_bvars(term_id, new_bvars) do
    %Term{type: original_type} = term = TF.get_term!(term_id)

    combined_bvars = new_bvars ++ term.bvars
    bvar_maxes = Enum.map(combined_bvars, & &1.name)
    new_max_num = Enum.max([term.max_num | bvar_maxes], fn -> 0 end)

    new_bvar_types = Enum.map(new_bvars, & &1.type)
    new_type = Type.new(original_type, new_bvar_types)

    new_bvar_tvars =
      Enum.reduce(new_bvars, MapSet.new(), fn bv, acc ->
        MapSet.union(acc, Type.free_type_vars(bv.type))
      end)

    new_tvars = MapSet.union(term.tvars, new_bvar_tvars)

    wrapped_term = %Term{
      term
      | bvars: combined_bvars,
        type: new_type,
        max_num: new_max_num,
        tvars: new_tvars
    }

    TF.memoize(wrapped_term)
  end

  @doc """
  Returns `true` when two rigid bound-variable heads refer to the same
  binder slot in their respective terms (modulo independent renaming of
  the surrounding lambdas).
  """
  @spec same_bound_slot?(Term.t(), Declaration.bound_var_t(), Term.t(), Declaration.bound_var_t()) ::
          boolean()
  def same_bound_slot?(left_term, left_head, right_term, right_head) do
    left_slot = bound_slot(left_term, left_head)
    right_slot = bound_slot(right_term, right_head)

    left_head.type == right_head.type and
      not is_nil(left_slot) and left_slot == right_slot
  end

  @doc """
  Computes the absolute slot of a bound-variable head inside a term's list
  of `:bvars`. Returns `nil` when the head does not refer to any of the
  term's own binders. Falls back to a `max_num`-based heuristic when the
  head's de Bruijn index is ambiguous wrt the listed binders.
  """
  @spec bound_slot(Term.t(), Declaration.bound_var_t()) :: integer() | nil
  def bound_slot(%Term{bvars: bvars, max_num: max_num}, %Declaration{name: name, type: type}) do
    exact_index =
      Enum.find_index(bvars, fn bv ->
        bv.name == name and bv.type == type
      end)

    if exact_index do
      exact_index
    else
      matching_by_type =
        bvars
        |> Enum.with_index()
        |> Enum.filter(fn {bv, _idx} -> bv.type == type end)

      case matching_by_type do
        [{_bv, idx}] -> idx
        _ -> max_num - name
      end
    end
  end
end
