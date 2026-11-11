import Carlet.K4HQuadraticExtractionProbe
import Carlet.K4QuadraticCoeffThreeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- The second monic quadratic may have arbitrary coefficient polynomials. -/
theorem k4H_no_monic_quadratic_factorization_with_homogeneous_first
    (a b c d e : K) (E D : Polynomial K)
    (hf : k4HQuartic K =
      (X^2 + C (k4QA K a b)*X + C (k4QB K c d e)) *
      (X^2 + C E*X + C D)) : False := by
  have hAE : k4QA K a b + E = 0 := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 3) hf.symm
    rw [quadratic_product_coeff_three] at ht
    unfold k4HQuartic at ht
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero _ 2
  have hE : E = k4QA K a b := by linear_combination hAE - (k4QA K a b)*h2
  subst E
  exact k4H_no_monic_homogeneous_quadratic_factorization K a b c d e D hf

#print axioms k4H_no_monic_quadratic_factorization_with_homogeneous_first
end Carlet
