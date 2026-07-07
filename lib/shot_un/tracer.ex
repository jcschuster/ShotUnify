defmodule ShotUn.Tracer do
  @moduledoc false
  # ETS-backed accumulator for `ShotUn.Trace.Node` records.
  #
  # Each public API call that opts into `vis: true` calls `start/0`,
  # which allocates a fresh unnamed `:public` ETS table and registers
  # its reference under `:shot_un_tracer` in the calling process's
  # dictionary. Concurrent unification calls from independent processes
  # therefore get independent tables and never share state.
  #
  # The table holds:
  #   * one `{:next_id, integer()}` counter row, incremented atomically
  #     by `:ets.update_counter/4` to allocate node ids without
  #     coordination, and
  #   * one `{id, %ShotUn.Trace.Node{}}` row per recorded node.
  #
  # Workers spawned within one search can share the parent's tracer
  # table by reading the parent's `current_table/0` and calling
  # `attach/1` from inside their own process — every Tracer.record/2
  # call from then on writes into the same table. This is the migration
  # path for future parallelization of the DFS engines.
  #
  # When tracing is off (`Process.get(:shot_un_tracer) == nil`),
  # `record/2` and `collect/1` are constant-time no-ops; the `attrs_fn`
  # thunk passed to `record/2` is *not* invoked, so formatting costs
  # are skipped entirely.

  alias ShotDs.Data.{Declaration, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.LatexFormatter
  alias ShotUn.Trace
  alias ShotUn.Trace.Node

  @key :shot_un_tracer
  @counter_key :next_id
  @aliases_key :shot_un_aliases

  @doc """
  Allocate a fresh per-call ETS table and install its reference in the
  current process's dictionary. Concurrent callers get independent
  tables.
  """
  @spec start() :: :ok
  def start do
    table =
      :ets.new(:shot_un_tracer, [
        :set,
        :public,
        {:write_concurrency, true},
        {:read_concurrency, true}
      ])

    Process.put(@key, table)
    Process.put(@aliases_key, %{})
    :ok
  end

  @doc """
  Tear down the per-call ETS table owned by this process. Safe to call
  when no tracer is active.
  """
  @spec stop() :: :ok
  def stop do
    Process.delete(@aliases_key)

    case Process.get(@key) do
      nil ->
        :ok

      table ->
        try do
          :ets.delete(table)
        rescue
          ArgumentError -> :ok
        end

        Process.delete(@key)
        :ok
    end
  end

  @spec active?() :: boolean()
  def active?, do: Process.get(@key) != nil

  @doc """
  Returns the current tracer ETS table reference (or `nil`). Use this
  to hand the tracer to a spawned worker so it can call `attach/1`
  inside its own process.
  """
  @spec current_table() :: :ets.tid() | nil
  def current_table, do: Process.get(@key)

  @doc """
  Install a tracer table reference (obtained from `current_table/0` in
  another process) in the current process's dictionary. From here on,
  this process's `record/2` calls write into that table. The table is
  *not* owned by this process, so do not call `stop/0` from here.
  """
  @spec attach(:ets.tid() | nil) :: :ok
  def attach(nil), do: :ok

  def attach(table) do
    Process.put(@key, table)
    :ok
  end

  @doc """
  Remove the tracer reference from this process's dictionary without
  destroying the table. Pair with `attach/1` in worker code.
  """
  @spec detach() :: :ok
  def detach do
    Process.delete(@key)
    :ok
  end

  @doc """
  Record a node as a child of `parent_id` (pass `nil` for the root).
  `attrs_fn` is a 0-arity thunk returning the attrs map; it is **only
  invoked when tracing is active**, so callers can do their term
  formatting inside the thunk without paying for it under `vis: false`.
  Returns the newly allocated node id, or `nil` when tracing is off.

  ID allocation uses `:ets.update_counter/4`, which is atomic — many
  processes sharing the same tracer table can call `record/2` in
  parallel and each will get a unique id.
  """
  @spec record(non_neg_integer() | nil, (-> map())) :: non_neg_integer() | nil
  def record(parent_id, attrs_fn) when is_function(attrs_fn, 0) do
    case Process.get(@key) do
      nil ->
        nil

      table ->
        id = :ets.update_counter(table, @counter_key, {2, 1}, {@counter_key, -1})
        attrs = attrs_fn.()
        node = struct(Node, Map.merge(attrs, %{id: id, parent_id: parent_id}))
        :ets.insert(table, {id, node})
        id
    end
  end

  @doc """
  Shorthand for `record(parent_id, fn -> %{kind: :fail, rule: rule} end)`.
  Lets engine call sites record a failure leaf without introducing a
  nested anonymous function (and the credo nesting warning it would
  trigger).
  """
  @spec record_fail(non_neg_integer() | nil, atom()) :: non_neg_integer() | nil
  def record_fail(parent_id, rule), do: record(parent_id, build_fail(rule))

  @spec record_fail(non_neg_integer() | nil, atom(), String.t()) ::
          non_neg_integer() | nil
  def record_fail(parent_id, rule, note), do: record(parent_id, build_fail(rule, note))

  defp build_fail(rule), do: fn -> %{kind: :fail, rule: rule} end
  defp build_fail(rule, note), do: fn -> %{kind: :fail, rule: rule, note: note} end

  @doc """
  Build a `ShotUn.Trace` tree from the accumulated nodes. Returns `nil`
  when tracing was never started in this process. Does not stop
  tracing — callers must invoke `stop/0` themselves. Children are
  ordered by id, which matches the order in which they were recorded
  (ids come from the atomic counter).
  """
  @spec collect(Trace.algorithm()) :: Trace.t() | nil
  def collect(algorithm) do
    case Process.get(@key) do
      nil ->
        nil

      table ->
        nodes =
          table
          |> :ets.tab2list()
          |> Enum.flat_map(fn
            {@counter_key, _} -> []
            {_id, %Node{} = node} -> [node]
          end)
          |> Enum.sort_by(& &1.id)

        by_id = Map.new(nodes, &{&1.id, &1})

        children_map =
          Enum.reduce(nodes, %{}, fn n, acc ->
            Map.update(acc, n.parent_id, [n.id], &(&1 ++ [n.id]))
          end)

        root_id =
          case Map.get(children_map, nil) do
            [id | _] -> id
            _ -> nil
          end

        %Trace{algorithm: algorithm, root: build_tree(root_id, by_id, children_map)}
    end
  end

  defp build_tree(nil, _, _), do: nil

  defp build_tree(id, by_id, children_map) do
    node = Map.fetch!(by_id, id)
    child_ids = Map.get(children_map, id, [])
    %{node | children: Enum.map(child_ids, &build_tree(&1, by_id, children_map))}
  end

  ##############################################################################
  # FORMATTING HELPERS — called while the term-factory scratchpad is alive.
  ##############################################################################

  @spec format_term(integer()) :: String.t()
  def format_term(id) when is_integer(id) do
    fvars = fvars_of_term(id)
    with_scoped_aliases(fvars, fn -> LatexFormatter.format!(id, hide_types: true) end)
  rescue
    _ -> "<term:#{id}>"
  end

  @spec format_pairs([{integer(), integer()}]) :: [{String.t(), String.t()}]
  def format_pairs(pairs) do
    Enum.map(pairs, fn {l, r} -> {format_term(l), format_term(r)} end)
  end

  @spec format_subst(Substitution.t()) :: String.t()
  def format_subst(%Substitution{fvar: fvar, term_id: term_id} = subst) do
    fvars = [fvar | fvars_of_term(term_id)]
    with_scoped_aliases(fvars, fn -> LatexFormatter.format!(subst, hide_types: true) end)
  rescue
    _ -> "<subst>"
  end

  @spec format_substs([Substitution.t()]) :: [String.t()]
  def format_substs(substs) do
    Enum.map(substs, &format_subst/1)
  end

  ##############################################################################
  # FRESH-VARIABLE ALIASING
  #
  # Fresh higher-order metas are stored with `reference()` names in
  # their `Declaration`. `LatexFormatter` would otherwise fall back to
  # `V_{short_ref(ref)}` — unreadable strings like `V_{1S4IST}`.
  #
  # When a tracer session is active, each new ref-named fvar is
  # interned into a per-call map (keyed by `@aliases_key` in the
  # process dict) with a raw-LaTeX nickname `H^{n}`. That map is then
  # installed via `LatexFormatter.with_latex_aliases/2` for the
  # duration of each format call, so `LatexFormatter` splices the
  # nickname in verbatim (no `escape_name` — braces would otherwise be
  # escaped to `\{`/`\}` and break the `^{…}` superscript group).
  #
  # `map_size(map) + 1` gives stable numbering within one tracer
  # session: any given ref keeps the same superscript across every
  # place it appears in the trace.
  ##############################################################################

  defp fvars_of_term(id) when is_integer(id) do
    case TF.get_term(id) do
      {:ok, %{fvars: fvars}} -> MapSet.to_list(fvars)
      _ -> []
    end
  end

  defp with_scoped_aliases(fvars, fmt_fn) do
    case Process.get(@aliases_key) do
      nil ->
        fmt_fn.()

      current ->
        merged = intern_refs(current, fvars)
        if merged != current, do: Process.put(@aliases_key, merged)
        LatexFormatter.with_latex_aliases(merged, fmt_fn)
    end
  end

  defp intern_refs(current, fvars) do
    Enum.reduce(fvars, current, fn
      %Declaration{name: n}, acc when is_reference(n) ->
        if Map.has_key?(acc, n) do
          acc
        else
          Map.put(acc, n, "H^{" <> Integer.to_string(map_size(acc) + 1) <> "}")
        end

      _decl, acc ->
        acc
    end)
  end

  @doc """
  LaTeX for a raw constant name (used in `note` fields). Wraps the name
  in `\\mathrm{…}` so it renders upright in math mode, matching how
  `LatexFormatter` renders non-logical constants.
  """
  @spec format_const_name(String.t() | atom()) :: String.t()
  def format_const_name(name) do
    escaped =
      name
      |> to_string()
      |> String.replace("_", ~S(\_))
      |> String.replace("#", ~S(\#))
      |> String.replace("$", ~S(\$))
      |> String.replace("%", ~S(\%))
      |> String.replace("&", ~S(\&))
      |> String.replace("{", ~S(\{))
      |> String.replace("}", ~S(\}))

    "\\mathrm{" <> escaped <> "}"
  end
end
