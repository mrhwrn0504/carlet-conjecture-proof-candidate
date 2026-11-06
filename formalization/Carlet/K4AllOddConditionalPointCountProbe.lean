import Carlet.K4SmallOddRangeProbe
import Carlet.K4PointCountConditionalBridgeProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

/-- Coverage bookkeeping for k=4: the five odd degrees below 17 are already
    handled by explicit constructions. Above that cutoff, the displayed
    Θ₄ point-count estimate is the only remaining geometric input. This is
    intentionally conditional and does not claim that estimate. -/
theorem hasZeroSumSubspace_four_of_odd_card_and_theta4_bound
    (n : ℕ) (hn : Odd n) (hn7 : 7 ≤ n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
    (hcard : Fintype.card K = 2^n)
    (hbound : 17 ≤ n →
      (Fintype.card K : ℝ)^3 -
        48 * Real.sqrt (Fintype.card K : ℝ) * (Fintype.card K : ℝ)^2 -
        40960 * (Fintype.card K : ℝ)^2 ≤
      (Fintype.card {x : Fin 4 → K //
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} : ℝ)) :
    HasZeroSumSubspace K 4 := by
  by_cases hn17 : 17 ≤ n
  · have hq : 131072 ≤ Fintype.card K := by
      rw [hcard]
      calc
        131072 = 2^17 := by norm_num
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn17
    exact k4_from_explicit_geometric_bound hq (hbound hn17)
  · exact k4_all_small_odd_degrees n hn hn7 (by omega) K hcard

#print axioms hasZeroSumSubspace_four_of_odd_card_and_theta4_bound
end Carlet
