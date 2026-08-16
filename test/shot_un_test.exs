defmodule ShotUnTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.UnifSolution

  test "unify/2 produces a direct substitution for a rigid pair" do
    x = TF.make_free_var_term("X", type_i())
    c = TF.make_const_term("c", type_i())
    x_decl = TF.get_term!(x).head

    [solution] = ShotUn.unify({x, c}) |> Enum.to_list()

    assert %UnifSolution{substitutions: [%{fvar: ^x_decl, term_id: ^c}], flex_pairs: []} =
             solution

    assert to_string(solution) == "substitutions: [X ↦ c]; remaining flex-flex pairs: []"
  end

  test "unify/2 keeps flex-flex pairs as deferred constraints" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())

    [solution] = ShotUn.unify({x, y}) |> Enum.to_list()

    assert %UnifSolution{substitutions: [], flex_pairs: [{^x, ^y}]} = solution
    assert to_string(solution) == "substitutions: []; remaining flex-flex pairs: [X =? Y]"
  end

  test "unify/2 explores all imitation and projection branches" do
    x = TF.make_free_var_term("X", type_iii())
    f = TF.make_const_term("f", type_iii())
    a = TF.make_const_term("a", type_i())

    solutions = ShotUn.unify({app(x, [a, a]), app(f, [a, a])}) |> Enum.to_list()

    assert length(solutions) == 9

    assert Enum.all?(solutions, fn %UnifSolution{substitutions: substs, flex_pairs: flex_pairs} ->
             length(substs) == 1 and flex_pairs == []
           end)

    assert MapSet.new(Enum.map(solutions, &to_string/1)) |> MapSet.size() == 9
  end
end
