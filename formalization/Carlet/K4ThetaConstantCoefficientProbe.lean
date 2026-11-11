import Carlet.K4ThetaLinearCoefficientProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet

theorem theta4_constant_coefficient_eq :
    (theta4PolynomialEquiv theta4).coeff 0 = k4H^2 := by
  have hX1 : (MvPolynomial.finSuccEquiv (ZMod 2) 3) (MvPolynomial.X (1 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 3)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ZMod 2) (n := 3) (j := (0 : Fin 3)))
  have hX2 : (MvPolynomial.finSuccEquiv (ZMod 2) 3) (MvPolynomial.X (2 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 3)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ZMod 2) (n := 3) (j := (1 : Fin 3)))
  have hX3 : (MvPolynomial.finSuccEquiv (ZMod 2) 3) (MvPolynomial.X (3 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 3)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ZMod 2) (n := 3) (j := (2 : Fin 3)))
  simp [theta4PolynomialEquiv, theta4, k4X, k4H,
    MvPolynomial.renameEquiv, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero,
    Equiv.swap_apply_def, hX1, hX2, hX3, Polynomial.coeff_add, Polynomial.coeff_mul]
  simp only [← map_pow, Polynomial.coeff_C] 
  norm_num
  have : CharP ThetaCoeffRing 2 := charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* ThetaCoeffRing)
    exact MvPolynomial.C_injective _ _) 2
  have h2 : (2 : ThetaCoeffRing) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : ThetaCoeffRing) = 1 := by linear_combination h2
  have h5 : (5 : ThetaCoeffRing) = 1 := by linear_combination (2 : ThetaCoeffRing)*h2
  have h4 : (4 : ThetaCoeffRing) = 0 := by linear_combination (2 : ThetaCoeffRing)*h2
  ring_nf
  simp [h2, h3, h4, h5]

#print axioms theta4_constant_coefficient_eq
end Carlet
