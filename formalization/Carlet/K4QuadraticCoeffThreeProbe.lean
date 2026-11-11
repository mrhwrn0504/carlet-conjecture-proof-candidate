import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable {R : Type*} [CommRing R]

theorem quadratic_product_coeff_three (A B E D : R) :
    ((X^2 + C A*X + C B) * (X^2 + C E*X + C D) : Polynomial R).coeff 3 = A+E := by
  have hprod :
      (X^2 + C A*X + C B) * (X^2 + C E*X + C D) =
      (X^4 + C (A+E)*X^3 + C (B+D+A*E)*X^2 +
        C (A*D+E*B)*X + C (B*D) : Polynomial R) := by
    simp only [map_add, map_mul]
    ring
  rw [hprod]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

#print axioms quadratic_product_coeff_three
end Carlet
