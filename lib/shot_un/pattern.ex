defmodule ShotUn.Pattern do
  @moduledoc """
  Higher-order pattern unification (Miller 1991).

  A higher-order *pattern* is a βη-normal term in which every free
  variable F occurs only in applications of the form
  $F(x_1, \\dots, x_n)$ where the arguments $x_1, \\dots, x_n$ are
  pairwise distinct bound variables. Unification over the pattern
  fragment is decidable and *unitary*: when a unifier exists it is
  unique up to α-renaming, so this entry point returns either a single
  most-general unifier or `:error`.

  The implementation realises Miller's algorithm with four rules:

    * *decomposition* of rigid-rigid pairs whose heads agree,
    * *inversion* of a flex–rigid pair $F(\\bar x) \\overset{?}{=} t$,
      with *pruning* of any nested flex application whose arguments
      would otherwise reach a binder outside $\\{\\bar x\\}$,
    * *alias* for flex–flex pairs with the same head — bind the
      variable to a fresh meta over the positions on which the two
      argument lists agree,
    * *intersection* for flex–flex pairs with distinct heads — bind
      both variables to a fresh meta applied to the bound variables
      they share.

  Termination is by structural recursion on the work-list; no depth
  bound is needed.

  Use `ShotUn.pattern_unify/2` as the public entry point. Inputs
  containing non-pattern terms raise `ArgumentError`. Pass `vis: true`
  in `opts` to receive a `{result, %ShotUn.Trace{}}` tuple.
  """

  alias ShotDs.Data.{Declaration, Substitution, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics
  alias ShotUn.{Fragment, Internal, Tracer, UnifSolution}

  @typep term_pair :: {Term.term_id(), Term.term_id()}

  @doc """
  Returns `{:ok, %UnifSolution{}}` (whose `flex_pairs` are always empty)
  when an MGU exists, otherwise `:error`. Raises `ArgumentError` when
  the input is not a higher-order pattern.

  `opts`:

    * `:vis` — when `true`, returns `{result, %ShotUn.Trace{}}` instead
      of `result`. Defaults to `false`.
  """
  @spec unify([term_pair()] | term_pair(), keyword()) ::
          {:ok, UnifSolution.t()}
          | :error
          | {{:ok, UnifSolution.t()} | :error, ShotUn.Trace.t()}
  def unify(pair_or_pairs, opts \\ [])

  def unify({l, r}, opts) when is_integer(l) and is_integer(r), do: unify([{l, r}], opts)

  def unify(pairs, opts) when is_list(pairs) do
    validate!(pairs)

    vis? = Keyword.get(opts, :vis, false)
    if vis?, do: Tracer.start()

    try do
      result = run_unify(pairs)

      if vis? do
        trace = :pattern |> Tracer.collect() |> ShotUn.Trace.prune_to_solutions()
        {result, trace}
      else
        result
      end
    after
      if vis?, do: Tracer.stop()
    end
  end

  defp run_unify(pairs) do
    my_scratchpad? = is_nil(Process.get(:term_scratchpad))
    if my_scratchpad?, do: TF.start_scratchpad()

    try do
      scope =
        for {l, r} <- pairs,
            id <- [l, r],
            fvar <- TF.get_term!(id).fvars,
            into: MapSet.new(),
            do: fvar

      root_id = Tracer.record(nil, build_root_attrs(pairs))

      case run(pairs, [], root_id) do
        {:ok, substs} ->
          cleaned = clean(substs, scope)
          committed = if my_scratchpad?, do: commit(cleaned), else: cleaned
          {:ok, %UnifSolution{substitutions: committed, flex_pairs: []}}

        :error ->
          :error
      end
    after
      if my_scratchpad?, do: TF.stop_scratchpad()
    end
  end

  defp validate!(pairs) do
    Enum.each(pairs, fn {l, r} ->
      unless Fragment.pattern?(l) and Fragment.pattern?(r) do
        raise ArgumentError,
          message:
            "ShotUn.Pattern.unify requires both sides of every pair to be " <>
              "higher-order patterns. Use ShotUn.unify/3 for the general case."
      end
    end)
  end

  ##############################################################################
  # WORK-LIST LOOP
  ##############################################################################

  @spec run([term_pair()], [Substitution.t()], non_neg_integer() | nil) ::
          {:ok, [Substitution.t()]} | :error
  defp run([], substs, parent_id) do
    _ = Tracer.record(parent_id, build_solved_attrs(substs))
    {:ok, substs}
  end

  defp run([{l, r} | rest], substs, parent_id) when l == r do
    new_id = Tracer.record(parent_id, build_trivial_attrs(rest, substs, l))
    run(rest, substs, new_id)
  end

  defp run([{l_id, r_id} | rest], substs, parent_id) do
    left = TF.get_term!(l_id)
    right = TF.get_term!(r_id)

    if left.type != right.type do
      _ =
        Tracer.record_fail(
          parent_id,
          :type_mismatch,
          "#{inspect(left.type)} vs #{inspect(right.type)}"
        )

      :error
    else
      dispatch(left, right, l_id, r_id, rest, substs, parent_id)
    end
  rescue
    _ -> record_fail_and_error(parent_id, :dead_end)
  end

  defp build_solved_attrs(substs) do
    fn ->
      %{kind: :solution, rule: :solved, substs: Tracer.format_substs(substs), flex: []}
    end
  end

  defp build_trivial_attrs(rest, substs, l) do
    fn ->
      %{
        kind: :step,
        rule: :trivial,
        pairs: Tracer.format_pairs(rest),
        substs: Tracer.format_substs(substs),
        flex: [],
        note: Tracer.format_term(l)
      }
    end
  end

  defp dispatch(left, right, l_id, r_id, rest, substs, parent_id) do
    case {left.head.kind, right.head.kind} do
      {l_kind, r_kind} when l_kind in [:co, :bv] and r_kind in [:co, :bv] ->
        decompose_rigid(left, right, rest, substs, parent_id)

      {:fv, :fv} ->
        if left.head == right.head do
          alias_rule(left, right, rest, substs, parent_id)
        else
          intersection_rule(left, right, rest, substs, parent_id)
        end

      {:fv, _} ->
        invert_pair(left, right, rest, substs, parent_id)

      {_, :fv} ->
        # Swap so the flex is on the left. The swap itself is bookkeeping;
        # the resulting rule (invert/alias/intersection) records the node.
        run([{r_id, l_id} | rest], substs, parent_id)

      _ ->
        record_fail_and_error(parent_id, :dead_end)
    end
  end

  ##############################################################################
  # RIGID-RIGID DECOMPOSITION
  ##############################################################################

  defp decompose_rigid(%Term{head: lh} = left, %Term{head: rh} = right, rest, substs, parent_id) do
    cond do
      lh.kind == :co and rh.kind == :co and lh == rh ->
        do_decompose(
          left,
          right,
          rest,
          substs,
          :decompose_const,
          Tracer.format_const_name(lh.name),
          parent_id
        )

      lh.kind == :bv and rh.kind == :bv and
          Internal.same_bound_slot?(left, lh, right, rh) ->
        do_decompose(left, right, rest, substs, :decompose_bv, nil, parent_id)

      true ->
        record_fail_and_error(parent_id, :rigid_clash)
    end
  end

  defp do_decompose(left, right, rest, substs, rule, note, parent_id) do
    case Internal.decompose(left, right) do
      {:ok, new_pairs} ->
        next_pairs = new_pairs ++ rest
        new_id = Tracer.record(parent_id, build_decompose_attrs(rule, next_pairs, substs, note))
        run(next_pairs, substs, new_id)

      :error ->
        record_fail_and_error(parent_id, :no_decompose)
    end
  end

  defp build_decompose_attrs(rule, next_pairs, substs, note) do
    fn ->
      %{
        kind: :step,
        rule: rule,
        pairs: Tracer.format_pairs(next_pairs),
        substs: Tracer.format_substs(substs),
        flex: [],
        note: note
      }
    end
  end

  ##############################################################################
  # FLEX-RIGID INVERSION (with pruning)
  ##############################################################################

  defp invert_pair(%Term{head: f_head} = flex_term, rigid_term, rest, substs, parent_id) do
    case extract_arg_indices(flex_term) do
      {:ok, arg_indices} ->
        n = length(arg_indices)
        index_to_pos = arg_indices |> Enum.with_index(1) |> Map.new()

        case invert_root(rigid_term, index_to_pos, n, f_head) do
          {:ok, body_id, prunings} ->
            sigma_f = build_sigma(f_head, body_id, arg_indices)

            apply_and_continue(
              [sigma_f | prunings],
              rest,
              substs,
              :invert,
              fmt_subst(sigma_f),
              parent_id
            )

          {:error, :occurs} ->
            record_fail_and_error(parent_id, :occurs)

          {:error, _} ->
            record_fail_and_error(parent_id, :invert_fail)
        end

      {:error, _} ->
        record_fail_and_error(parent_id, :not_pattern)
    end
  end

  defp fmt_subst(sigma), do: fn -> Tracer.format_subst(sigma) end

  defp build_root_attrs(pairs) do
    fn ->
      %{
        kind: :start,
        rule: :init,
        pairs: Tracer.format_pairs(pairs),
        substs: [],
        flex: []
      }
    end
  end

  defp record_fail_and_error(parent_id, rule) do
    _ = Tracer.record_fail(parent_id, rule)
    :error
  end

  # Process the rigid term as σ(F)'s body: head and args are at "F's context
  # depth" (depth 0), and the term's outer bvars are NOT counted toward depth
  # — they're stripped away (they match F's wrapper lambdas on the LHS).
  defp invert_root(rigid_term, mapping, n, f_head) do
    case classify_head(rigid_term.head, 0, mapping, f_head) do
      :occurs_check ->
        {:error, :occurs}

      :unreachable ->
        {:error, :inversion_fail}

      {:rigid, new_head} ->
        case map_args(rigid_term.args, mapping, n, f_head, 0, []) do
          {:ok, new_args, prunings} ->
            new_term = build_stripped_term(rigid_term, new_head, new_args)
            {:ok, TF.memoize(new_term), prunings}

          err ->
            err
        end

      {:flex, _g_head} ->
        # The flex-flex cases (alias/intersection) handle this branch; if we
        # see a root flex on the rigid side of invert_pair, something upstream
        # mis-dispatched.
        {:error, :unexpected_root_flex}
    end
  end

  # Like `build_term`, but drops the original's outer bvars: they were F's
  # wrapper lambdas, not part of σ(F)'s body.
  defp build_stripped_term(original, new_head, new_args) do
    new_type = %Type{goal: original.type.goal, args: []}
    new_fvars = collect_fvars(new_head, new_args)
    new_consts = collect_consts(new_head, new_args)
    new_tvars = collect_tvars(new_head, new_args, [])
    new_max = collect_max_num(new_head, new_args, [])

    %Term{
      id: 0,
      head: new_head,
      args: new_args,
      bvars: [],
      type: new_type,
      fvars: new_fvars,
      consts: new_consts,
      tvars: new_tvars,
      max_num: new_max
    }
  end

  # If F's outer bvars (i.e. the wrapping lambdas of the LHS term) are part of
  # the pair's surrounding context, we treat them like any other context binders.
  # The returned indices are the outer-index of each arg in F's surrounding
  # context (counting from 1).
  defp extract_arg_indices(%Term{args: [], bvars: []} = _flex_term), do: {:ok, []}

  defp extract_arg_indices(%Term{args: args, bvars: bvars}) do
    n_wrap = length(bvars)

    indices =
      Enum.map(args, fn arg_id ->
        case Fragment.outer_bvar_index(arg_id) do
          :not_bvar -> :not_bvar
          idx -> idx
        end
      end)

    cond do
      Enum.any?(indices, &(&1 == :not_bvar)) ->
        {:error, :not_pattern}

      length(Enum.uniq(indices)) != length(indices) ->
        {:error, :not_pattern}

      Enum.any?(indices, fn idx -> idx > n_wrap and not free_bvar_ok?(idx) end) ->
        # Free bvars (those above F's wrapper bvars) are allowed; we don't
        # constrain them further.
        {:ok, indices}

      true ->
        {:ok, indices}
    end
  end

  # Reserved hook for future tightening; for now any outer bvar index is OK.
  defp free_bvar_ok?(_idx), do: true

  defp build_inverted_body(t_id, mapping, n, f_head, depth, prunings) do
    term = TF.get_term!(t_id)
    inner_d = depth + length(term.bvars)

    case classify_head(term.head, inner_d, mapping, f_head) do
      :occurs_check ->
        {:error, :occurs}

      {:flex, g_head} ->
        prune_and_rebuild(term, g_head, inner_d, mapping, n, f_head, depth, prunings)

      {:rigid, new_head} ->
        rebuild_rigid(term, new_head, inner_d, mapping, n, f_head, depth, prunings)

      :unreachable ->
        {:error, :inversion_fail}
    end
  end

  # Classify a head:
  #   :occurs_check  — head is F itself (the one we're inverting for)
  #   {:flex, h}     — head is some other free variable; pruning may apply
  #   {:rigid, h'}   — head is a constant, a local bvar (depth-relative), or
  #                    an outer bvar whose index is in `mapping`; h' is the
  #                    re-mapped head.
  #   :unreachable   — head is an outer bvar whose index is not in `mapping`.
  defp classify_head(%Declaration{kind: :fv} = head, _depth, _mapping, f_head)
       when head == f_head,
       do: :occurs_check

  defp classify_head(%Declaration{kind: :fv} = head, _depth, _mapping, _f_head),
    do: {:flex, head}

  defp classify_head(%Declaration{kind: :co} = head, _depth, _mapping, _f_head),
    do: {:rigid, head}

  defp classify_head(%Declaration{kind: :bv, name: k} = head, depth, mapping, _f_head) do
    if k <= depth do
      {:rigid, head}
    else
      outer = k - depth

      case Map.fetch(mapping, outer) do
        {:ok, pos} ->
          n = map_size(mapping)
          # In σ(F) = λu_1…u_n. body, u_pos has de Bruijn index (n - pos + 1).
          # Inside body at the current inner depth, that index is shifted by depth.
          new_k = n - pos + 1 + depth
          {:rigid, %Declaration{head | name: new_k}}

        :error ->
          :unreachable
      end
    end
  end

  # Constant, local bvar, or already-remapped outer bvar: recurse into args.
  defp rebuild_rigid(term, new_head, inner_d, mapping, n, f_head, _depth, prunings) do
    case map_args(term.args, mapping, n, f_head, inner_d, prunings) do
      {:ok, new_args, final_prunings} ->
        new_term = build_term(term, new_head, new_args, mapping, n)
        {:ok, TF.memoize(new_term), final_prunings}

      {:error, _} = err ->
        err
    end
  end

  # G's application: check which of G's primitive-bvar args remain valid
  # under the current `mapping`; if any are invalid, generate σ(G) = λv. G'(kept)
  # and recurse with G'.
  defp prune_and_rebuild(term, g_head, inner_d, mapping, n, f_head, _depth, prunings) do
    classified = Enum.map(term.args, &classify_flex_arg(&1, inner_d, mapping))

    cond do
      Enum.any?(classified, &(&1 == :not_pattern)) ->
        {:error, :not_pattern}

      not Enum.any?(classified, &(&1 == :prune)) ->
        rebuild_flex_kept(term, g_head, mapping, n, f_head, inner_d, prunings)

      true ->
        keep_positions = positions_to_keep(classified)
        rebuild_flex_pruned(term, g_head, keep_positions, mapping, n, f_head, inner_d, prunings)
    end
  end

  defp positions_to_keep(classified) do
    classified
    |> Enum.with_index(1)
    |> Enum.filter(fn {c, _} -> c != :prune end)
    |> Enum.map(fn {_, pos} -> pos end)
  end

  # All of G's args survive: remap them and rebuild the application with the
  # original G head.
  defp rebuild_flex_kept(term, g_head, mapping, n, f_head, inner_d, prunings) do
    with {:ok, new_args, final_prunings} <-
           map_args(term.args, mapping, n, f_head, inner_d, prunings) do
      new_term = build_term(term, g_head, new_args, mapping, n)
      {:ok, TF.memoize(new_term), final_prunings}
    end
  end

  # Some of G's args are out of reach for F's substitution: replace G with a
  # fresh G' of reduced arity (recording σ(G) in the accumulated prunings) and
  # rebuild the application around G' applied to the kept args.
  defp rebuild_flex_pruned(term, g_head, keep_positions, mapping, n, f_head, inner_d, prunings) do
    with {:ok, sigma_g, g_prime_head} <- generate_pruning(g_head, term.args, keep_positions),
         kept_arg_ids = Enum.map(keep_positions, &Enum.at(term.args, &1 - 1)),
         {:ok, new_args, final_prunings} <-
           map_args(kept_arg_ids, mapping, n, f_head, inner_d, prunings ++ [sigma_g]) do
      new_term = build_term(term, g_prime_head, new_args, mapping, n)
      {:ok, TF.memoize(new_term), final_prunings}
    end
  end

  # Classify a single argument of a flex application (encountered during
  # inversion of F).
  #
  #   :keep       — arg refers to a binder inside t (between F's level and
  #                 the current depth) or to a binder in F's context that is
  #                 in `mapping`. It survives inversion.
  #   :prune      — arg refers to a binder in F's context that is not in
  #                 `mapping`. It must be dropped from G's argument list.
  #   :not_pattern — arg is not a primitive bvar; this should have been caught
  #                  by `validate!`, but is checked defensively.
  defp classify_flex_arg(arg_id, depth, mapping) do
    arg = TF.get_term!(arg_id)
    arg_local = length(arg.bvars)

    case arg.head do
      %Declaration{kind: :bv, name: k} -> classify_bv_arg(k, arg_local, depth, mapping)
      _ -> :not_pattern
    end
  end

  # Classify a primitive bv argument by its de Bruijn index relative to the
  # arg's own eta-expansion lambdas, the surrounding t-internal depth, and the
  # inversion mapping for F's outer context.
  defp classify_bv_arg(k, arg_local, _depth, _mapping) when k <= arg_local,
    # The arg's head refers to one of its OWN eta-expansion lambdas — not a
    # primitive bvar in the surrounding context.
    do: :not_pattern

  defp classify_bv_arg(k, arg_local, depth, _mapping) when k - arg_local <= depth,
    # Refers to a t-internal binder between F's level and G's level.
    do: :keep

  defp classify_bv_arg(k, arg_local, depth, mapping) do
    outer = k - arg_local - depth

    if Map.has_key?(mapping, outer), do: :keep, else: :prune
  end

  # σ(G) = λv_1…v_m. G'(v_{p_1}, …, v_{p_l})
  defp generate_pruning(g_head, _original_args, keep_positions) do
    %Declaration{type: %Type{goal: g_goal, args: g_arg_types}} = g_head
    kept_types = Enum.map(keep_positions, &Enum.at(g_arg_types, &1 - 1))
    g_prime_type = Type.new(g_goal, kept_types)
    g_prime_head = Declaration.fresh_var(g_prime_type)

    # Build λv_1…v_m. G'(v_{p_1}, …, v_{p_l}).
    body = build_pruning_body(g_prime_head, g_arg_types, keep_positions)
    sigma = Substitution.new(g_head, body)
    {:ok, sigma, g_prime_head}
  rescue
    e -> {:error, e}
  end

  defp build_pruning_body(g_prime_head, g_arg_types, keep_positions) do
    # Fresh fvars for the m wrappers; eta-expanded primitive bvar terms for the
    # references G'(v_{p_1}, …, v_{p_l}).
    wrappers = Enum.map(g_arg_types, &Declaration.fresh_var/1)
    wrapper_terms = Enum.map(wrappers, &TF.make_term/1)

    g_prime_term = TF.make_term(g_prime_head)
    arg_terms = Enum.map(keep_positions, fn pos -> Enum.at(wrapper_terms, pos - 1) end)
    body_app = TF.fold_apply!(g_prime_term, arg_terms)

    # Abstract over the wrappers right-to-left so v_1 is the outermost binder.
    List.foldr(wrappers, body_app, fn wrap, acc -> TF.make_abstr_term!(acc, wrap) end)
  end

  defp map_args(arg_ids, mapping, n, f_head, depth, prunings) do
    Enum.reduce_while(arg_ids, {:ok, [], prunings}, fn arg_id, {:ok, acc, ps} ->
      case build_inverted_body(arg_id, mapping, n, f_head, depth, ps) do
        {:ok, new_id, new_ps} -> {:cont, {:ok, [new_id | acc], new_ps}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, rev, final_ps} -> {:ok, Enum.reverse(rev), final_ps}
      err -> err
    end
  end

  # Reassemble a term node from its (mapped) head and args, recomputing the
  # accessor fields. The bvars and type structure are inherited from the
  # original term (the inversion preserves the lambda-skeleton of t).
  defp build_term(%Term{} = original, new_head, new_args, _mapping, _n) do
    new_fvars = collect_fvars(new_head, new_args)
    new_consts = collect_consts(new_head, new_args)
    new_tvars = collect_tvars(new_head, new_args, original.bvars)
    new_max = collect_max_num(new_head, new_args, original.bvars)

    %Term{
      original
      | head: new_head,
        args: new_args,
        fvars: new_fvars,
        consts: new_consts,
        tvars: new_tvars,
        max_num: new_max
    }
  end

  ##############################################################################
  # FLEX-FLEX SAME HEAD (alias rule)
  ##############################################################################

  defp alias_rule(
         %Term{head: head, args: l_args, bvars: l_bvars},
         %Term{args: r_args, bvars: r_bvars},
         rest,
         substs,
         parent_id
       ) do
    # F(x_1, …, x_n) =? F(y_1, …, y_n). Wrap both arg lists in their
    # respective outer-bvar contexts so we get consistent outer indices.
    l_indices = Enum.map(l_args, &Fragment.outer_bvar_index/1)
    r_indices = Enum.map(r_args, &Fragment.outer_bvar_index/1)

    cond do
      Enum.any?(l_indices ++ r_indices, &(&1 == :not_bvar)) ->
        record_fail_and_error(parent_id, :not_pattern)

      length(l_indices) != length(r_indices) or l_bvars != r_bvars ->
        record_fail_and_error(parent_id, :rigid_clash)

      true ->
        common_positions =
          Enum.zip(l_indices, r_indices)
          |> Enum.with_index(1)
          |> Enum.filter(fn {{a, b}, _pos} -> a == b end)
          |> Enum.map(fn {_, pos} -> pos end)

        %Declaration{type: %Type{goal: f_goal, args: f_arg_types}} = head

        kept_types = Enum.map(common_positions, &Enum.at(f_arg_types, &1 - 1))
        f_prime_head = Declaration.fresh_var(Type.new(f_goal, kept_types))

        body = build_pruning_body(f_prime_head, f_arg_types, common_positions)
        sigma = Substitution.new(head, body)

        apply_and_continue([sigma], rest, substs, :alias, fmt_subst(sigma), parent_id)
    end
  end

  ##############################################################################
  # FLEX-FLEX DIFFERENT HEADS (intersection rule)
  ##############################################################################

  defp intersection_rule(
         %Term{head: f_head, args: l_args} = l_term,
         %Term{head: g_head, args: r_args} = r_term,
         rest,
         substs,
         parent_id
       ) do
    l_indices = Enum.map(l_args, &Fragment.outer_bvar_index/1)
    r_indices = Enum.map(r_args, &Fragment.outer_bvar_index/1)

    cond do
      Enum.any?(l_indices ++ r_indices, &(&1 == :not_bvar)) ->
        record_fail_and_error(parent_id, :not_pattern)

      l_term.bvars != r_term.bvars ->
        record_fail_and_error(parent_id, :rigid_clash)

      true ->
        common_indices = Enum.uniq(Enum.filter(l_indices, &(&1 in r_indices)))

        l_keep_pos =
          common_indices
          |> Enum.map(fn idx -> Enum.find_index(l_indices, &(&1 == idx)) + 1 end)

        r_keep_pos =
          common_indices
          |> Enum.map(fn idx -> Enum.find_index(r_indices, &(&1 == idx)) + 1 end)

        %Declaration{type: %Type{goal: goal, args: l_arg_types}} = f_head
        %Declaration{type: %Type{args: r_arg_types}} = g_head

        h_arg_types = Enum.map(l_keep_pos, &Enum.at(l_arg_types, &1 - 1))
        h_head = Declaration.fresh_var(Type.new(goal, h_arg_types))

        sigma_f =
          Substitution.new(f_head, build_pruning_body(h_head, l_arg_types, l_keep_pos))

        # For σ(G) the body is λv_1…v_m. H(v_{q_1}, …, v_{q_k}); we reuse the same
        # builder but with the right-side arg types and positions.
        sigma_g_body = build_pruning_body(h_head, r_arg_types, r_keep_pos)
        sigma_g = Substitution.new(g_head, sigma_g_body)

        note_fn = fn ->
          Tracer.format_subst(sigma_f) <> "; " <> Tracer.format_subst(sigma_g)
        end

        apply_and_continue([sigma_f, sigma_g], rest, substs, :intersection, note_fn, parent_id)
    end
  end

  ##############################################################################
  # SUBSTITUTION APPLICATION & ACCUMULATION
  ##############################################################################

  defp apply_and_continue(new_substs, rest, substs, rule, note_fn, parent_id) do
    {final_rest, final_substs} =
      Enum.reduce(new_substs, {rest, substs}, &apply_one_subst/2)

    new_id =
      Tracer.record(parent_id, build_continue_attrs(rule, final_rest, final_substs, note_fn))

    run(final_rest, final_substs, new_id)
  end

  defp apply_one_subst(sigma, {acc_rest, acc_substs}) do
    new_rest =
      Enum.map(acc_rest, fn {l, r} ->
        {Semantics.subst!(sigma, l), Semantics.subst!(sigma, r)}
      end)

    {new_rest, Semantics.add_subst!(acc_substs, sigma)}
  end

  defp build_continue_attrs(rule, final_rest, final_substs, note_fn) do
    fn ->
      %{
        kind: :step,
        rule: rule,
        pairs: Tracer.format_pairs(final_rest),
        substs: Tracer.format_substs(final_substs),
        flex: [],
        note: note_fn.()
      }
    end
  end

  ##############################################################################
  # SOLUTION POST-PROCESSING
  ##############################################################################

  defp clean(substs, scope) do
    for s <- substs, MapSet.member?(scope, s.fvar) do
      %{s | term_id: Semantics.subst!(substs, s.term_id)}
    end
  end

  defp commit(substs) do
    Enum.map(substs, fn s ->
      %{s | term_id: TF.commit_to_global!(s.term_id)}
    end)
  end

  ##############################################################################
  # FIELD RECOMPUTATION (mirrors ShotDs.Stt.Semantics.calc_new_* helpers)
  ##############################################################################

  defp collect_fvars(head, arg_ids) do
    head_set =
      case head do
        %Declaration{kind: :fv} -> MapSet.new([head])
        _ -> MapSet.new()
      end

    Enum.reduce(arg_ids, head_set, fn id, acc ->
      MapSet.union(acc, TF.get_term!(id).fvars)
    end)
  end

  defp collect_consts(head, arg_ids) do
    head_set =
      case head do
        %Declaration{kind: :co, name: name} ->
          if name in ShotDs.Hol.Definitions.signature(),
            do: MapSet.new(),
            else: MapSet.new([head])

        _ ->
          MapSet.new()
      end

    Enum.reduce(arg_ids, head_set, fn id, acc ->
      MapSet.union(acc, TF.get_term!(id).consts)
    end)
  end

  defp collect_tvars(head, arg_ids, bvars) do
    after_bvars =
      Enum.reduce(bvars, Type.free_type_vars(head.type), fn bv, acc ->
        MapSet.union(acc, Type.free_type_vars(bv.type))
      end)

    Enum.reduce(arg_ids, after_bvars, fn id, acc ->
      MapSet.union(acc, TF.get_term!(id).tvars)
    end)
  end

  defp collect_max_num(head, arg_ids, bvars) do
    head_max =
      case head do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    bvar_maxes = Enum.map(bvars, & &1.name)
    arg_maxes = Enum.map(arg_ids, fn id -> TF.get_term!(id).max_num end)
    Enum.max([head_max | arg_maxes ++ bvar_maxes], fn -> 0 end)
  end

  ##############################################################################
  # σ(F) CONSTRUCTION
  ##############################################################################

  # σ(F) = λu_1…λu_n. body, with each u_i typed after F's i-th parameter.
  # `body_id` is the already-inverted body — its bvar indices were chosen so
  # that, when these lambdas are prepended, they point to the right u_i.
  defp build_sigma(f_head, body_id, arg_indices) do
    n = length(arg_indices)

    if n == 0 do
      Substitution.new(f_head, body_id)
    else
      %Declaration{type: %Type{args: f_arg_types}} = f_head

      bvar_decls =
        f_arg_types
        |> Enum.take(n)
        |> Enum.with_index(1)
        |> Enum.map(fn {type, i} -> Declaration.new_bound_var(n - i + 1, type) end)

      %Term{} = body = TF.get_term!(body_id)

      combined_bvars = bvar_decls ++ body.bvars
      new_type = Type.new(body.type, Enum.map(bvar_decls, & &1.type))
      bvar_maxes = Enum.map(combined_bvars, & &1.name)
      new_max = Enum.max([body.max_num | bvar_maxes], fn -> 0 end)
      new_tvars = collect_tvars(body.head, body.args, combined_bvars)

      new_term = %Term{
        body
        | bvars: combined_bvars,
          type: new_type,
          tvars: new_tvars,
          max_num: new_max
      }

      Substitution.new(f_head, TF.memoize(new_term))
    end
  end
end
