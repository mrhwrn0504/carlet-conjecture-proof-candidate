import Carlet.K4ThetaFirstCoefficientBridgeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet

theorem factor_constants_cannot_both_be_divisible {R : Type*} [CommSemiring R]
    (h : R) (f g : Polynomial R) (hnot : ¬ h ∣ (f*g).coeff 1) :
    ¬ (h ∣ f.coeff 0 ∧ h ∣ g.coeff 0) := by
  rintro ⟨hf, hg⟩
  apply hnot
  have hformula : (f*g).coeff 1 = f.coeff 0*g.coeff 1 + f.coeff 1*g.coeff 0 := by
    rw [Polynomial.coeff_mul]
    simp [Finset.Nat.antidiagonal_succ]
  rw [hformula]
  exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right hg _)

variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

theorem k4Theta_factor_constants_not_both_divisible
    (f g : Polynomial (MvPolynomial (Fin 3) K))
    (hcoeff : (f*g).coeff 1 = ((theta4PolynomialEquiv theta4).coeff 1).map
      (algebraMap (ZMod 2) K)) :
    ¬ (k4HOver K ∣ f.coeff 0 ∧ k4HOver K ∣ g.coeff 0) := by
  apply factor_constants_cannot_both_be_divisible
  rw [hcoeff]
  exact k4H_not_dvd_theta4_linear_coefficient K

#print axioms factor_constants_cannot_both_be_divisible
#print axioms k4Theta_factor_constants_not_both_divisible
end Carlet
