import Carlet.K4ThetaConstantCoefficientProbe
import Carlet.K4HCoefficientObstructionProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

theorem k4H_not_dvd_theta4_linear_coefficient :
    ¬ k4HOver K ∣ ((theta4PolynomialEquiv theta4).coeff 1).map
      (algebraMap (ZMod 2) K) := by
  rw [theta4_linear_coefficient_eq]
  simpa [theta4LinearCoeff] using k4H_not_dvd_linear_coefficient K

theorem k4Theta_constant_coefficient_over :
    ((theta4PolynomialEquiv theta4).coeff 0).map (algebraMap (ZMod 2) K) =
      (k4HOver K)^2 := by
  rw [theta4_constant_coefficient_eq]
  simp [k4HOver]

#print axioms k4Theta_constant_coefficient_over
#print axioms k4H_not_dvd_theta4_linear_coefficient
end Carlet
