import Carlet.K4NormOneThetaBridgeProbe
import Carlet.K4SmallOddRangeProbe
import Carlet.LowDimensionReduction
import Mathlib.Tactic

noncomputable section
namespace Carlet

theorem hasZeroSumSubspace_four_of_odd_card
    (n : ℕ) (hn : Odd n) (hmin : 7≤n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K=2^n) : HasZeroSumSubspace K 4 := by
  classical
  by_cases hsmall : n<17
  · exact k4_all_small_odd_degrees n hn hmin hsmall K hcard
  · have hlarge : 11≤n := by omega
    exact k4NormOneTheta_hasZeroSum_four_large n hn hlarge
      (finrank_eq_of_card n hcard)

/-- Once the remaining k=5 family is supplied, the original conjecture
    follows with the k=4 family discharged by this file. -/
theorem oddCarletConjecture_of_five
    (h5 : ∀ (n : ℕ), Odd n → 11≤n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K=2^n → HasZeroSumSubspace K 5) :
    OddCarletConjecture := by
  classical
  apply oddCarletConjecture_iff_small_dimensions.mpr
  intro n k hn hk hk5 hbound K _ _ _ hcard
  have hfin := finrank_eq_of_card (K:=K) n hcard
  have hkCases : k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hkCases with rfl | rfl | rfl
  · exact hasZeroSumSubspace_three n hfin hn (by omega)
  · exact hasZeroSumSubspace_four_of_odd_card n hn (by omega) K hcard
  · exact h5 n hn (by omega) K hcard

#print axioms hasZeroSumSubspace_four_of_odd_card
#print axioms oddCarletConjecture_of_five

end Carlet
