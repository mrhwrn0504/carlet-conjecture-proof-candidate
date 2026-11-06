import Carlet.K4CoeffRecursionProbe
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
open Polynomial MvPolynomial
namespace Carlet

lemma coeff_one_P4 : k4UniversalP4.coeff 1 =
    k4UniversalP3.eval (k4UniversalX 3) * k4UniversalP3.coeff 1 := by
  rw [k4UniversalP4, Polynomial.coeff_add, coeff_one_sq_char_two _ coeff_zero_P3]
  simp only [Polynomial.coeff_C_mul]
  simp

lemma coeff_two_P4 : k4UniversalP4.coeff 2 =
    k4UniversalP3.coeff 1 ^ 2 +
      k4UniversalP3.eval (k4UniversalX 3) * k4UniversalP3.coeff 2 := by
  rw [k4UniversalP4, Polynomial.coeff_add, coeff_two_sq_char_two _ coeff_zero_P3]
  simp only [Polynomial.coeff_C_mul]

def k4UnitTuple : K4FreeIndex → ZMod 2 :=
  fun i => if i = 0 then 1 else 0

theorem k4UniversalP4_coeff_two_eval_unit :
    MvPolynomial.eval k4UnitTuple (k4UniversalP4.coeff 2) = 0 := by
  rw [coeff_two_P4, coeff_one_P3, coeff_two_P3]
  simp [k4UnitTuple, k4UniversalP1, k4UniversalP2, k4UniversalP3,
    k4UniversalX]

theorem k4_coeff_two_not_theta4 : k4UniversalP4.coeff 2 ≠ theta4 := by
  intro h
  have he := congrArg (MvPolynomial.eval k4UnitTuple) h
  have ht : MvPolynomial.eval k4UnitTuple theta4 = 1 := by
    change MvPolynomial.eval
      (fun i : K4FreeIndex => if i = 0 then 1 else 0) theta4 = 1
    exact theta4_eval_first_unit
  rw [k4UniversalP4_coeff_two_eval_unit, ht] at he
  norm_num at he

#print axioms k4UniversalP4_coeff_two_eval_unit
#print axioms k4_coeff_two_not_theta4
end Carlet
