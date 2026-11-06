import Carlet.N13K5SubfieldProbe
import Carlet.N13K4FourCertificate
import Carlet.RemainingCases11
import Carlet.FourDimension15
import Mathlib.Tactic
namespace Carlet
theorem hasZeroSumSubspace_five_of_13_dvd_card {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n : ℕ) (hcard : Fintype.card K = 2 ^ n)
    (hdiv : 13 ∣ n) : HasZeroSumSubspace K 5 := by
  exact hasZeroSumSubspace_five_of_13_dvd_probe n (finrank_eq_of_card n hcard) hdiv

/-- Residual ranges after also closing the k=5 family 13 | n. -/
theorem oddCarletConjecture_iff_four_and_five_7_11_13_15_31_remaining :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 15 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_four_and_five_7_11_15_31_remaining.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with ⟨hk, h7, h15⟩ | ⟨hk, h5, h11, h21, h31⟩
    · by_cases hdiv13 : 13 ∣ n
      · subst k
        exact hasZeroSumSubspace_four_of_13_dvd_card n hcard hdiv13
      · exact h n k hn (Or.inl ⟨hk, h7, hdiv13, h15⟩) hb K hcard
    · by_cases hdiv13 : 13 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_13_dvd_card n hcard hdiv13
      · exact h n k hn (Or.inr ⟨hk, h5, h11, hdiv13, h21, h31⟩) hb K hcard
#print axioms oddCarletConjecture_iff_four_and_five_7_11_13_15_31_remaining
end Carlet


