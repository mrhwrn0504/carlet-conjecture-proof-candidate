import Carlet.K4HQuarticRootDegreeProbe
import Carlet.K4QuadraticNormalFormProbe
import Carlet.K4HLinearRootProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem k4HQuartic_eval_linear (a b : K) :
    (k4HQuartic K).eval (k4QA K a b) = k4HLinearTest K a b := by
  simp only [k4HQuartic, k4QP, k4QA, k4HLinearTest, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : Polynomial K) = 1 := by linear_combination h2
  ring_nf
  simp [h2, h3]

theorem k4HQuartic_no_polynomial_root (A : Polynomial K) :
    (k4HQuartic K).eval A ≠ 0 := by
  intro hz
  have heq : A^4 + k4QP K*A^2 + (X : Polynomial K)*(X+1)*A + (k4QP K)^2 = 0 := by
    simpa [k4HQuartic] using hz
  have hd := k4HQuartic_root_degree_le_one K A heq
  have hnorm := k4Polynomial_normal_linear K A hd
  rw [hnorm, k4HQuartic_eval_linear] at hz
  exact k4HLinearTest_ne_zero K (A.coeff 1) (A.coeff 0) hz

#print axioms k4HQuartic_eval_linear
#print axioms k4HQuartic_no_polynomial_root
end Carlet
