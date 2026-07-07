defmodule ShotUn.MatchingTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  alias ShotDs.Data.{Declaration, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.{Matching, UnifSolution}

  describe "match/1" do
    test "direct primitive binding" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())
      x_decl = TF.get_term!(x).head

      [sol] = Matching.match({x, c}) |> Enum.to_list()

      assert %UnifSolution{substitutions: [%{fvar: ^x_decl, term_id: ^c}], flex_pairs: []} = sol
    end

    test "rigid-rigid decomposition" do
      a = TF.make_const_term("a", type_i())
      f = TF.make_const_term("f", type_ii())
      fa1 = app(f, a)
      fa2 = app(f, a)

      assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
               Matching.match({fa1, fa2}) |> Enum.to_list()
    end

    test "enumerates all 9 imitation/projection branches at order 1" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())

      sols = Matching.match({app(x, [a, a]), app(f, [a, a])}) |> Enum.to_list()

      assert length(sols) == 9
      assert Enum.all?(sols, &match?(%UnifSolution{flex_pairs: []}, &1))

      assert MapSet.size(MapSet.new(Enum.map(sols, &to_string/1))) == 9
    end

    test "drops a variable that the pattern never consumes" do
      x = TF.make_free_var_term("X", type_ii())
      y = TF.make_free_var_term("Y", type_i())
      a = TF.make_const_term("a", type_i())

      sols = Matching.match({app(x, y), a}) |> Enum.to_list()

      # Both imitation (X ↦ λu. a) and projection (X ↦ λu. u then Y ↦ a) work.
      refute Enum.empty?(sols)

      assert Enum.any?(sols, fn %UnifSolution{substitutions: substs} ->
               Enum.any?(substs, fn s -> s.fvar.name == "X" end)
             end)
    end

    test "rejects non-ground target" do
      x = TF.make_free_var_term("X", type_i())
      y = TF.make_free_var_term("Y", type_i())

      assert_raise ArgumentError, ~r/ground/, fn ->
        Matching.match({x, y}) |> Enum.to_list()
      end
    end

    test "rejects higher-than-second-order types" do
      # F : (i → i) → i  — order 2; ok.
      # G : ((i → i) → i) → i  — order 3; not ok.
      g_type = Type.new(:i, [Type.new(:i, [Type.new(:i, :i)])])
      g = TF.make_free_var_term("G", g_type)

      target = TF.make_const_term("c", type_i())

      assert_raise ArgumentError, ~r/second-order/, fn ->
        # apply g to anything ground; we just need it to type-check at i.
        # Build a closed argument of type (i → i) → i:
        # arg = λh : i→i. c
        h = Declaration.new_free_var("H", Type.new(:i, :i))
        body_id = TF.make_const_term("c", type_i())
        arg = TF.make_abstr_term!(body_id, h)

        Matching.match({app(g, arg), target}) |> Enum.to_list()
      end
    end

    test "fails cleanly when constants differ" do
      a = TF.make_const_term("a", type_i())
      b = TF.make_const_term("b", type_i())

      assert [] == Matching.match({a, b}) |> Enum.to_list()
    end
  end
end
