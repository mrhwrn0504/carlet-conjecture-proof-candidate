import Carlet.Theta5RankFourSpanBridgeProbe
import Carlet.LowDimensionalK5Assembly

noncomputable section
namespace Carlet

/-- Conditional assembly: the only hypothesis is the still-unproved Θ₅
    independent-zero family after removing degrees already covered by
    subfield constructions. This does not assert that family exists. -/
theorem oddCarletConjecture_of_remaining_theta5_independent_zeros
    (hpoint : ∀ (n : ℕ), Odd n → 37 ≤ n →
      ¬ 5 ∣ n → ¬ 9 ∣ n → ¬ 11 ∣ n → ¬ 13 ∣ n → ¬ 17 ∣ n →
      ¬ 19 ∣ n → ¬ 21 ∣ n → ¬ 23 ∣ n → ¬ 29 ∣ n → ¬ 31 ∣ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n →
        ∃ x : Fin 5 → K, LinearIndependent (ZMod 2) x ∧
          MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0) :
    OddCarletConjecture := by
  apply oddCarletConjecture_of_five_large
  intro n hn hmin K _ _ _ hcard
  classical
  by_cases h5 : 5 ∣ n
  · exact hasZeroSumSubspace_five_of_dvd n (finrank_eq_of_card n hcard) h5
  by_cases h9 : 9 ∣ n
  · exact hasZeroSumSubspace_five_of_9_dvd n (finrank_eq_of_card n hcard) h9
  by_cases h11 : 11 ∣ n
  · exact hasZeroSumSubspace_five_of_11_dvd_card n hcard h11
  by_cases h13 : 13 ∣ n
  · exact hasZeroSumSubspace_five_of_13_dvd_card n hcard h13
  by_cases h17 : 17 ∣ n
  · exact hasZeroSumSubspace_five_of_17_dvd_card n hcard h17
  by_cases h19 : 19 ∣ n
  · exact hasZeroSumSubspace_five_of_19_dvd_card n hcard h19
  by_cases h21 : 21 ∣ n
  · exact hasZeroSumSubspace_five_of_21_dvd n (finrank_eq_of_card n hcard) h21
  by_cases h23 : 23 ∣ n
  · exact hasZeroSumSubspace_five_of_23_dvd_card n hcard h23
  by_cases h29 : 29 ∣ n
  · exact hasZeroSumSubspace_five_of_29_dvd_card n hcard h29
  by_cases h31 : 31 ∣ n
  · exact hasZeroSumSubspace_five_of_31_dvd n (finrank_eq_of_card n hcard) h31
  obtain ⟨x, hx, htheta⟩ :=
    hpoint n hn hmin h5 h9 h11 h13 h17 h19 h21 h23 h29 h31 K hcard
  exact hasZeroSumSubspace_five_of_theta5_independent_zero x hx htheta

#print axioms oddCarletConjecture_of_remaining_theta5_independent_zeros
end Carlet
