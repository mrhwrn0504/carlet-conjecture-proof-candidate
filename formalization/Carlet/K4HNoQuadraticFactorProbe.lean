import Carlet.K4QuadraticGeneralFactorProbe
import Carlet.K4QuadraticProductCoefficientsProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem k4HQuartic_no_monic_quadratic_product (A B E D : Polynomial K)
    (hf : k4HQuartic K = (X^2+C A*X+C B)*(X^2+C E*X+C D)) : False := by
  have hthree : A+E = 0 := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 3) hf.symm
    rw [quadratic_product_coeff_three] at ht
    unfold k4HQuartic at ht
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have htwo : B+D+A*E = k4QP K := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 2) hf.symm
    rw [quadratic_product_coeff_two] at ht
    unfold k4HQuartic at ht
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hone : A*D+E*B = (X : Polynomial K)*(X+1) := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 1) hf.symm
    rw [quadratic_product_coeff_one] at ht
    unfold k4HQuartic at ht
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hzero : B*D = (k4QP K)^2 := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 0) hf.symm
    rw [quadratic_product_coeff_zero] at ht
    unfold k4HQuartic at ht
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero _ 2
  have heq : E = A := by linear_combination hthree - A*h2
  subst E
  have hs : B+D = k4QP K + A^2 := by
    linear_combination htwo - A^2*h2
  have ha : A*(B+D) = (X : Polynomial K)*(X+1) := by linear_combination hone
  exact k4H_quadratic_equations_general_impossible K A B D hs ha hzero

#print axioms k4HQuartic_no_monic_quadratic_product
end Carlet
