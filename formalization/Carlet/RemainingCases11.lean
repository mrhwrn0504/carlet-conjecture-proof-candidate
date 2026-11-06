import Carlet.N11K5SubfieldProbe
import Carlet.FourDimension15
import Mathlib.Tactic

namespace Carlet

/-- The 11-divisible k=5 family under the original finite-field cardinality hypothesis. -/
theorem hasZeroSumSubspace_five_of_11_dvd_card {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n : ℕ) (hcard : Fintype.card K = 2 ^ n)
    (hdiv : 11 ∣ n) : HasZeroSumSubspace K 5 := by
  exact hasZeroSumSubspace_five_of_11_dvd_probe n (finrank_eq_of_card n hcard) hdiv

/-- The original conjecture is reduced further by the 11-divisible k=5 family. -/
theorem oddCarletConjecture_iff_four_and_five_7_11_15_31_remaining :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 15 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_four_and_five_7_15_31_remaining.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with ⟨hk, h7, h15⟩ | ⟨hk, h5, h21, h31⟩
    · exact h n k hn (Or.inl ⟨hk, h7, h15⟩) hb K hcard
    · by_cases h11 : 11 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_11_dvd_card n hcard h11
      · exact h n k hn (Or.inr ⟨hk, h5, h11, h21, h31⟩) hb K hcard

#print axioms hasZeroSumSubspace_five_of_11_dvd_card
#print axioms oddCarletConjecture_iff_four_and_five_7_11_15_31_remaining

end Carlet
