import Carlet.K4SmallOddRangeProbe
import Carlet.K4PointCountConditionalBridgeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet

/-- This reduction is conditional on the displayed geometric point estimate. -/
theorem k4_all_odd_assuming_geometric_estimate
    (n : ℕ) (hn : Odd n) (hmin : 7 ≤ n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
    (hcard : Fintype.card K = 2^n)
    (hbound : 17 ≤ n → (Fintype.card K : ℝ)^3 -
      48*Real.sqrt (Fintype.card K : ℝ)*(Fintype.card K : ℝ)^2 -
      40960*(Fintype.card K : ℝ)^2 ≤
      (Fintype.card {x : Fin 4 → K //
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} : ℝ)) :
    HasZeroSumSubspace K 4 := by
  classical
  by_cases hsmall : n < 17
  · exact k4_all_small_odd_degrees n hn hmin hsmall K hcard
  · have hn17 : 17 ≤ n := by omega
    have hp : 2^17 ≤ 2^n := Nat.pow_le_pow_right (by omega) hn17
    have hq : 131072 ≤ Fintype.card K := by rw [hcard]; norm_num at hp ⊢; exact hp
    exact k4_from_explicit_geometric_bound hq (hbound hn17)

#print axioms k4_all_odd_assuming_geometric_estimate
end Carlet

