import Carlet.Frobenius23Base
import Mathlib.Algebra.Field.ZMod
open Polynomial
noncomputable section
lemma irreducible_degree_dvd_frobPoly (g : P17) (hi : Irreducible g) (n : Nat) :
    g.natDegree ∣ n ↔ g ∣ frobPoly n - X := by
  have hf : frobPoly n = (X:P17)^(Nat.card F17 ^ n) := by
    rw [frobPoly_eq_pow]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hf]
  exact hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := n)
#print axioms irreducible_degree_dvd_frobPoly
