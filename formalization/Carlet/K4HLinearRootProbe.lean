import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- H(X,1,aX+b), the affine-linear-root test for the ternary quartic. -/
def k4HLinearTest (a b : K) : Polynomial K :=
  let x : Polynomial K := X
  let z : Polynomial K := C a * X + C b
  x^4 + 1 + z^4 + x^2 + x^2*z^2 + z^2 + x*z*(x+1+z)

theorem k4HLinearTest_normal (a b : K) :
    k4HLinearTest K a b =
      C (a^4+a^2+1) * X^4 + C (a*(a+1)) * X^3 +
      C (1+b^2+b+a+a^2) * X^2 + C (b^2+b)*X + C (1+b^4+b^2) := by
  unfold k4HLinearTest
  simp only [map_add, map_mul, map_pow, map_one]
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero (Polynomial K) 2
  have h4 : (4 : Polynomial K) = 0 := by linear_combination (2 : Polynomial K)*h2
  have h6 : (6 : Polynomial K) = 0 := by linear_combination (3 : Polynomial K)*h2
  ring_nf
  simp [h2, h4, h6]

theorem k4HLinearTest_coeff_three (a b : K) :
    (k4HLinearTest K a b).coeff 3 = a*(a+1) := by
  rw [k4HLinearTest_normal]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

theorem k4HLinearTest_coeff_four (a b : K) :
    (k4HLinearTest K a b).coeff 4 = a^4+a^2+1 := by
  rw [k4HLinearTest_normal]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

/-- No homogeneous linear substitution z = ax + by annihilates H. -/
theorem k4HLinearTest_ne_zero (a b : K) : k4HLinearTest K a b ≠ 0 := by
  intro hz
  have hthree : a*(a+1) = 0 := by
    rw [← k4HLinearTest_coeff_three K a b, hz]
    simp
  have hfour : a^4+a^2+1 = 0 := by
    rw [← k4HLinearTest_coeff_four K a b, hz]
    simp
  rcases mul_eq_zero.mp hthree with ha | ha
  · simp [ha] at hfour
  · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have ha' : a = 1 := by linear_combination ha - h2
    rw [ha'] at hfour
    have h : (1 : K) = 0 := by linear_combination hfour - h2
    exact one_ne_zero h

#print axioms k4HLinearTest_ne_zero
#print axioms k4HLinearTest_normal
#print axioms k4HLinearTest_coeff_three
#print axioms k4HLinearTest_coeff_four
end Carlet

