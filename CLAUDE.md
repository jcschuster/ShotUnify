# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
mix deps.get                       # fetch deps (shot_ds, credo, dialyxir, ex_doc)
mix compile
mix test                           # run the full suite
mix test test/shot_un/pattern_test.exs            # one file
mix test test/shot_un/pattern_test.exs:42         # one test by line
mix test --only describe:"flex-rigid"             # by tag
mix format
mix credo --all                    # CI runs `mix credo` (without --all)
mix dialyzer                       # type/contract checks (slow first run)
mix docs                           # ex_doc output in doc/
mix run bench/benchmark.exs        # unification micro-benchmarks
mix run bench/overhead.exs         # scratchpad/factory overhead probe
```

CI (`.github/workflows/elixir.yml`) runs `mix credo`, `mix dialyzer`, `mix test` on Elixir 1.20 / OTP 28. Match that toolchain locally when reproducing failures.

## Architecture

ShotUn implements three higher-order unification algorithms over terms supplied by the `shot_ds` library. Terms are not values; they are integer IDs (`Term.term_id()`) into `ShotDs.Stt.TermFactory` (`TF`). All algorithms manipulate IDs and ask `TF` to materialise terms when they need to inspect heads, args, or bvars.

### Module layout

- `ShotUn` (`lib/shot_un.ex`) — public API and the depth-bounded **pre-unification** engine (Huet 1975). Also the strategy dispatcher for `unify/3`.
- `ShotUn.Pattern` (`lib/shot_un/pattern.ex`) — **Miller pattern unification** (decidable, unitary). Four rules: rigid–rigid decomposition, flex–rigid inversion with pruning of nested flex apps, flex–flex same-head (alias), flex–flex different-head (intersection). Validates input via `Fragment.pattern?/1`; raises `ArgumentError` on non-patterns.
- `ShotUn.Matching` (`lib/shot_un/matching.ex`) — **Huet second-order matching**. Lazy stream of all matchers; preconditions: RHS ground, every type order ≤ 2.
- `ShotUn.Fragment` (`lib/shot_un/fragment.ex`) — classifiers used by `:auto` dispatch and by `validate!` in the two decidable engines: `type_order/1`, `ground?/1`, `bounded_order?/2`, `pattern?/1`, `pattern_problem?/1`, `matching_problem?/1`, and `outer_bvar_index/1` (key helper that returns the surrounding-context index of a primitive bvar arg, or `:not_bvar`).
- `ShotUn.Bindings` (`lib/shot_un/bindings.ex`) — generates imitation and projection substitutions used by both the pre-unification engine and the matching engine.
- `ShotUn.Internal` (`lib/shot_un/internal.ex`) — shared, state-agnostic helpers operating purely on term IDs: `decompose/2` (zips rigid–rigid arg lists wrapped in parent binders), `wrap_in_bvars/2`, `same_bound_slot?/4`, `bound_slot/2`.
- `ShotUn.UnifSolution` (`lib/shot_un/unif_solution.ex`) — result struct (`substitutions` + `flex_pairs`) with a `String.Chars` impl using `ShotDs.Util.Formatter`.
- `ShotUn.Trace` (`lib/shot_un/trace.ex`) + `ShotUn.Trace.Node` — decision-tree result returned by every public entry point when `vis: true` is passed in `opts`. Pre-pruned to only the paths from the root to a `:solution` leaf via `Trace.prune_to_solutions/1`.
- `ShotUn.Tracer` (`lib/shot_un/tracer.ex`, `@moduledoc false`) — ETS-backed accumulator. `Tracer.start/0` allocates a fresh `:public` unnamed ETS table per API call and registers it under `:shot_un_tracer` in the calling process's dict, so concurrent `vis: true` calls from independent processes never share state. Node ids come from `:ets.update_counter/4` (atomic; safe under parallel writers); rows are `{id, %Node{}}`. The three engines call `Tracer.record/2` on every transition with a 0-arity thunk — when tracing is off the thunk is **not** invoked, so format costs are skipped (this is what keeps `vis: false` overhead at the bench-noise level). `current_table/0` + `attach/1` + `detach/0` are exposed so future parallel workers can inherit the parent's tracer without a process-dict copy.
- `ShotUn.Trace.Mermaid` (`lib/shot_un/trace/mermaid.ex`) — renders a `Trace` as a `graph TD` diagram. `==>` for branching choice points, `-.->` for linear continuations; classDefs for `start`/`step`/`solution`/`fail` node kinds. Modeled on `ShotTx.Proof.to_mermaid/2`.

### Strategy dispatch

`ShotUn.unify/3` takes `:strategy` ∈ `:pre_unification` (default), `:auto`, `:pattern`, `:matching`. `:auto` calls `Fragment.pattern_problem?` first, then `Fragment.matching_problem?`, falling back to pre-unification with the supplied depth bound. `ShotUn.pattern_unify/1` and `ShotUn.match/1` are direct entry points; the latter is a lazy `Stream`.

### Search engine pattern (pre-unification and matching)

Both engines share the same shape:

1. `Stream.resource/3` opens a `TF.start_scratchpad()`, snapshots the **initial fvar scope** of the problem, and runs a DFS over a stack of `search_state` maps (`pairs`, `substs`, `flex`/depth).
2. `explore_branch/1` dispatches each frame's head pair through `step → evaluate_pair`, which matches on the head kinds (`:co`, `:bv`, `:fv`) and either decomposes, binds, or branches into imitation/projection candidates via `Bindings.generic_binding/3`.
3. When a solution is found, `clean_solution` projects the substitution list onto the *initial* fvar scope (dropping bindings for intermediate fresh variables) and `commit_solution` lifts the term IDs out of the scratchpad with `TF.commit_to_global!/1`. The scratchpad is torn down by the resource's `after` callback.

Pre-unification additionally carries a `flex` list of deferred flex–flex pairs and a `depth` counter that is decremented on each imitation/projection branch (the only source of unbounded search).

### Pattern unification specifics

`ShotUn.Pattern.unify/1` runs a single work-list loop (no branching) and only opens a scratchpad if one isn't already active in the process dictionary (`Process.get(:term_scratchpad)`). When invoked nested inside another scratchpad it returns un-committed IDs so the caller can reuse them. Inversion (`invert_root → build_inverted_body`) walks the RHS tracking a `depth` (inner binders), a `mapping` from outer bvar indices to σ(F) parameter positions, and an accumulator of pruning substitutions for nested flex heads whose arg lists must be narrowed.

### Working with terms

Use `TF.get_term!(id)` to materialise a term, and the helpers in `ShotDs.Stt.TermFactory` (`make_term`, `make_fresh_var_term`, `fold_apply!`, `make_abstr_term!`, `memoize`) to build new ones. New term construction must happen inside a scratchpad; the engines manage that lifecycle for callers. `ShotDs.Stt.Semantics.subst!/2` and `add_subst!/2` are the canonical substitution-application primitives.

### Tests

`test/shot_un/` mirrors the lib layout (`bindings_test.exs`, `dispatch_test.exs`, `matching_test.exs`, `pattern_test.exs`). `test/shot_un_test.exs` exercises the public `ShotUn.unify` surface; `shot_un_coverage_test.exs` targets uncovered branches. Tests use `async: false` because they share the `TF` global store.
