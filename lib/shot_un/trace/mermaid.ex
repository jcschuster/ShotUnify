defmodule ShotUn.Trace.Mermaid do
  @moduledoc """
  Renders a `ShotUn.Trace` as a Mermaid `graph TD` diagram.

  Terms, substitutions and pair sides are rendered as LaTeX via
  `ShotDs.Util.LatexFormatter` and embedded inside a single `$$…$$`
  math block per label. Multi-line labels use `\\begin{aligned}…`
  `\\end{aligned}` with an empty `&` at the head of each row for left
  alignment; prose (headers, "(empty σ)", …) lives inside `\\text{…}`.
  All LaTeX fragments are maximally grouped in `{…}` so stray `_`, `^`
  or `\\lambda` produced by the formatter bind only to the token they
  belong to.

  Two renderer quirks are worked around at the label-generation layer,
  because Mermaid's Kino/Livebook pipeline hits them both:

    * **`\\` row separators are halved.** Mermaid's quoted-label parser
      treats `\\` as an escape and emits a single `\`. That would
      collapse the KaTeX row break to a literal control-space. We emit
      `\\\\` (four backslashes) so Mermaid halves it back to the `\\`
      KaTeX expects.

    * **`~` and `\\ ` produce `&nbsp;` in the KaTeX HTML.** That
      entity is undefined in SVG's XML DTD and breaks "Save as SVG"
      downloads with `error … Entity 'nbsp' not defined`. Both are
      rewritten to `\\,` (thin space, rendered via CSS margin, no HTML
      entity in the DOM).

  `<br/>` HTML line breaks are **not** used — Mermaid drops them once
  the label parser hits `$$…$$`, collapsing everything onto one line.
  Everything lives inside the single math environment instead.

  Edge styling mirrors `ShotTx.Proof.to_mermaid/2`: branching choice
  points (multiple children) use solid arrows (`==>`); linear
  continuations use dotted arrows (`-.->`). Node colours encode the
  node kind — start (blue), step (gray), solution (green), fail
  (orange).

  ## Options

    * `:show_state` — include the work-list (and accumulated σ for
      solution leaves) in each node's label. Defaults to `true`.
  """

  alias ShotUn.Trace
  alias ShotUn.Trace.Node

  @header """
  %%{init: {'theme': 'base', 'themeVariables': { 'lineColor': '#999999', 'edgeLabelBackground': '#ffffff', 'fontFamily': 'sans-serif'}}}%%
  graph TD;
    classDef start fill:#e3f2fd,stroke:#1565c0,stroke-width:2px,color:#0d47a1,rx:8px,ry:8px;
    classDef step fill:#eeeeee,stroke:#999999,stroke-width:2px,color:#333333,rx:8px,ry:8px;
    classDef solution fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px,color:#1b5e20,rx:8px,ry:8px;
    classDef fail fill:#fff3e0,stroke:#cc5500,stroke-width:2px,color:#000000,rx:8px,ry:8px;
  """

  @spec render(Trace.t(), keyword()) :: String.t()
  def render(trace, opts \\ [])

  def render(%Trace{root: nil}, _opts), do: ""

  def render(%Trace{root: root}, opts) do
    show_state? = Keyword.get(opts, :show_state, true)

    {nodes, edges} = collect(root, [], [], show_state?)

    node_lines =
      Enum.map_join(nodes, "\n", fn {id, label, class} ->
        "  N#{id}[\"#{label}\"]:::#{class};"
      end)

    edge_lines =
      Enum.map_join(edges, "\n", fn
        {from, to, :branch} -> "  N#{from} ==> N#{to};"
        {from, to, :linear} -> "  N#{from} -.-> N#{to};"
      end)

    @header <> node_lines <> "\n" <> edge_lines <> "\n"
  end

  ##############################################################################
  # TREE WALK
  ##############################################################################

  defp collect(%Node{} = node, nodes, edges, show_state?) do
    self_entry = {node.id, label_for(node, show_state?), class_for(node)}
    nodes = nodes ++ [self_entry]
    edge_kind = if length(node.children) > 1, do: :branch, else: :linear

    Enum.reduce(node.children, {nodes, edges}, fn child, {ns, es} ->
      child_edge = {node.id, child.id, edge_kind}
      collect(child, ns, es ++ [child_edge], show_state?)
    end)
  end

  defp class_for(%Node{kind: :start}), do: "start"
  defp class_for(%Node{kind: :solution}), do: "solution"
  defp class_for(%Node{kind: :fail}), do: "fail"
  defp class_for(%Node{kind: :step}), do: "step"

  ##############################################################################
  # LABEL BUILDERS — each label is one $$…$$ block.
  ##############################################################################

  defp label_for(%Node{kind: :start} = n, show?) do
    body = if show?, do: pair_lines(n.pairs), else: []
    wrap_math([tex_text("(#{n.id}) init") | body])
  end

  defp label_for(%Node{kind: :solution} = n, show?) do
    head = tex_text("(#{n.id}) ★ solution")

    body =
      if show? do
        subst_lines(n.substs) ++ flex_lines(n.flex)
      else
        []
      end

    wrap_math([head | body])
  end

  defp label_for(%Node{kind: :fail} = n, _show?) do
    base = "(#{n.id}) ⊥ #{rule_name(n.rule)}"

    line =
      if n.note do
        tex_text(base <> ":") <> "\\;" <> sanitize(n.note)
      else
        tex_text(base)
      end

    wrap_math([line])
  end

  defp label_for(%Node{kind: :step} = n, show?) do
    head = tex_text("(#{n.id}) #{rule_name(n.rule)}")
    note_line = if n.note, do: [sanitize(n.note)], else: []
    body = if show?, do: pair_lines(n.pairs), else: []
    wrap_math([head | note_line ++ body])
  end

  # Single $$…$$ block per label. Multiple lines go through
  # `\begin{aligned}` (works in both inline and display math, unlike
  # `gathered` which needs display mode — Mermaid uses inline for
  # `$$…$$`). Each row is written as `& body`, with `&` as the (empty)
  # alignment marker so KaTeX left-aligns the row.
  #
  # The `\\` row separator is emitted as four backslashes in the label
  # source. Mermaid's quoted-label parser treats `\\` as an escape and
  # halves it to `\`, which would collapse the KaTeX row break to a
  # single backslash. Emitting `\\\\` survives that halving and lets
  # KaTeX see the `\\` it needs.
  defp wrap_math([single]), do: "$${" <> single <> "}$$"

  defp wrap_math(lines) do
    body = Enum.map_join(lines, "\\\\\\\\", &("&" <> &1))
    "$$\\begin{aligned}" <> body <> "\\end{aligned}$$"
  end

  # Prose rendered as one `\text{…}` run *per word*, joined by `\;`.
  # A single `\text{a b}` would make KaTeX emit `<mtext>a&nbsp;b</mtext>`
  # in its MathML — every literal space inside `\text{…}` becomes
  # `&nbsp;`, and `&nbsp;` isn't defined in SVG's XML DTD, so the
  # exported diagram fails to parse. Splitting keeps every text run
  # single-word, so no interior spaces make it into `<mtext>`.
  defp tex_text(s) do
    case s |> to_string() |> String.split(" ", trim: true) do
      [] -> "\\text{}"
      words -> Enum.map_join(words, "\\;", &("\\text{" <> escape_text(&1) <> "}"))
    end
  end

  defp escape_text(s) do
    s
    |> to_string()
    |> String.replace("\\", "\\textbackslash{}")
    |> String.replace("{", "\\{")
    |> String.replace("}", "\\}")
    |> String.replace("$", "\\$")
    |> String.replace("#", "\\#")
    |> String.replace("&", "\\&")
    |> String.replace("_", "\\_")
    |> String.replace("%", "\\%")
  end

  defp pair_lines([]), do: [tex_text("(no pending pairs)")]
  defp pair_lines(pairs), do: Enum.map(pairs, &pair_line/1)

  # Kino's KaTeX build renders neither `\overset{?}{=}` nor
  # `\stackrel{?}{=}` — both come back as an empty `<mo></mo>` in the
  # generated MathML. Fall back to `=^?`, which is just a raw
  # superscript on `=` and always renders.
  @eqq "=^?"

  @bullet "\\bullet"

  defp pair_line({l, r}) do
    @bullet <> "\\,{" <> sanitize(l) <> "}" <> @eqq <> "{" <> sanitize(r) <> "}"
  end

  defp subst_lines([]), do: [tex_text("(empty") <> "\\;\\sigma\\text{)}"]

  defp subst_lines(substs) do
    Enum.map(substs, fn s -> @bullet <> "\\," <> sanitize(s) end)
  end

  defp flex_lines([]), do: []

  defp flex_lines(pairs) do
    strs =
      Enum.map(pairs, fn {l, r} ->
        "{" <> sanitize(l) <> "}" <> @eqq <> "{" <> sanitize(r) <> "}"
      end)

    [tex_text("flex:") <> "\\;" <> Enum.join(strs, ";\\,")]
  end

  # Sanitize a LaTeX string on its way into a Mermaid label:
  #
  #   * `"` and newlines break the Mermaid label parser (labels are
  #     already inside `"…"`).
  #   * `~` (LaTeX non-breaking space) and `\ ` (LaTeX control-space)
  #     both make KaTeX emit the HTML entity `&nbsp;`, which is
  #     undefined in SVG's XML DTD and breaks "Save as SVG" downloads.
  #     Rewrite both to `\,` (a thin space rendered via CSS margin —
  #     no HTML entity in the DOM).
  defp sanitize(text) do
    text
    |> to_string()
    |> String.replace("\"", "&quot;")
    |> String.replace("\n", " ")
    |> String.replace("~", "\\,")
    |> String.replace("\\ ", "\\,")
  end

  defp rule_name(nil), do: "?"
  defp rule_name(:init), do: "init"
  defp rule_name(:trivial), do: "trivial"
  defp rule_name(:decompose_const), do: "decompose (const)"
  defp rule_name(:decompose_bv), do: "decompose (bv)"
  defp rule_name(:bind), do: "bind"
  defp rule_name(:flex_flex), do: "flex-flex defer"
  defp rule_name(:imitation), do: "imitation"
  defp rule_name(:projection), do: "projection"
  defp rule_name(:invert), do: "invert"
  defp rule_name(:alias), do: "alias"
  defp rule_name(:intersection), do: "intersection"
  defp rule_name(:type_mismatch), do: "type mismatch"
  defp rule_name(:rigid_clash), do: "rigid clash"
  defp rule_name(:occurs), do: "occurs check"
  defp rule_name(:no_decompose), do: "decompose fail"
  defp rule_name(:depth_exhausted), do: "depth exhausted"
  defp rule_name(:invert_fail), do: "inversion fail"
  defp rule_name(:not_pattern), do: "not a pattern"
  defp rule_name(:dead_end), do: "dead end"
  defp rule_name(:solved), do: "solved"
  defp rule_name(other), do: to_string(other)
end
