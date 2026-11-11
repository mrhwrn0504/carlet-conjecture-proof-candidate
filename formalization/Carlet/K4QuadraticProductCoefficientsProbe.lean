import Carlet.K4QuadraticCoeffThreeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable {R : Type*} [CommRing R]

theorem quadratic_product_normal (A B E D : R) :
      (X^2 + C A*X + C B) * (X^2 + C E*X + C D) =
      (X^4 + C (A+E)*X^3 + C (B+D+A*E)*X^2 +
        C (A*D+E*B)*X + C (B*D) : Polynomial R) := by
    simp only [map_add, map_mul]
    ring

theorem quadratic_product_coeff_two (A B E D : R) :
    ((X^2+C A*X+C B)*(X^2+C E*X+C D) : Polynomial R).coeff 2 = B+D+A*E := by
  rw [quadratic_product_normal]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

theorem quadratic_product_coeff_one (A B E D : R) :
    ((X^2+C A*X+C B)*(X^2+C E*X+C D) : Polynomial R).coeff 1 = A*D+E*B := by
  rw [quadratic_product_normal]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

theorem quadratic_product_coeff_zero (A B E D : R) :
    ((X^2+C A*X+C B)*(X^2+C E*X+C D) : Polynomial R).coeff 0 = B*D := by
  rw [quadratic_product_normal]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

#print axioms quadratic_product_coeff_two
#print axioms quadratic_product_coeff_one
#print axioms quadratic_product_coeff_zero
end Carlet
