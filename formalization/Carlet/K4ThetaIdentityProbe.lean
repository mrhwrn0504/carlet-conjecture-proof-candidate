import Carlet.K4CoeffEightProbe
import Mathlib.Tactic.LinearCombination
noncomputable section
open Polynomial MvPolynomial
namespace Carlet
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : CharP K4FreeRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* K4FreeRing)
    exact MvPolynomial.C_injective _ _) 2

theorem k4UniversalP4_coeff_eight_eq_theta4 :
    k4UniversalP4.coeff 8 = theta4 := by
  rw [coeff_eight_P4, coeff_four_P3, coeff_two_P2]
  simp only [k4UniversalP1, k4UniversalP2, k4UniversalP3,
    k4UniversalX, theta4, k4X, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  have h2 : (2 : K4FreeRing) = 0 := CharP.cast_eq_zero K4FreeRing 2
  linear_combination ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 6 +
      (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 6 +
      (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 4 +
      (MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 7 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 4 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 7 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 6 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 6 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 5 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 5 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 4 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 4 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 3 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 7 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 6 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 6 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 5 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 5 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 4 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) +
      (6 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 4 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) +
      (6 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 3 +
      (6 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) +
      (5 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 6 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 5 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 5 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 4 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) +
      (5 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) +
      (8 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) +
      (8 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (5 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) +
      (8 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 5 +
      (MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 4 +
      (MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3 +
      (5 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 +
      (6 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (5 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) +
      (9 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 4 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 3 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (3 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) +
      (8 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) ^ 3 +
      (MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) ^ 2 +
      (MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) +
      (5 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (1 : Fin 4)) ^ 2 +
      (2 : K4FreeRing) * (MvPolynomial.X (0 : Fin 4)) ^ 7 * (MvPolynomial.X (1 : Fin 4))) * h2

#print axioms k4UniversalP4_coeff_eight_eq_theta4
end Carlet
