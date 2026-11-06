import Carlet.K4PointCountArithmeticProbe
import Carlet.K4ThetaIndependentBridgeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

/-- Conditional connection only: the geometric lower bound is an explicit
    hypothesis and is not established by this theorem. -/
theorem k4_from_explicit_geometric_bound (hq : 131072 ≤ Fintype.card K)
    (hbound : (Fintype.card K : ℝ)^3 -
      48*Real.sqrt (Fintype.card K : ℝ)*(Fintype.card K : ℝ)^2 -
      40960*(Fintype.card K : ℝ)^2 ≤
      (Fintype.card {x : Fin 4 → K //
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} : ℝ)) :
    HasZeroSumSubspace K 4 := by
  apply hasZeroSumSubspace_four_of_theta4_large_zero_count
  exact k4_explicit_point_bound_implies_large_count _ _ hq hbound

#print axioms k4_from_explicit_geometric_bound
end Carlet
