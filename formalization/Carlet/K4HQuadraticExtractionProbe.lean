import Carlet.K4HQuadraticObstructionProbe
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def k4QA (a b : K) : Polynomial K := C a * X + C b
def k4QB (c d e : K) : Polynomial K := C c * X^2 + C d * X + C e
def k4QP : Polynomial K := X^2 + X + 1

theorem k4QA_eqn_normal (a b : K) :
    k4QA K a b * (k4QP K + (k4QA K a b)^2) =
      C (a^3+a)*X^3 + C (a+b+a^2*b)*X^2 +
      C (a+b+a*b^2)*X + C (b^3+b) := by
  unfold k4QA k4QP
  simp only [map_add, map_mul, map_pow]
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero (Polynomial K) 2
  have h3 : (3 : Polynomial K) = 1 := by linear_combination h2
  ring_nf
  simp [h3]

theorem k4QB_eqn_normal (a b c d e : K) :
    k4QB K c d e * (k4QB K c d e + k4QP K + (k4QA K a b)^2) =
      C (c*(c+(1+a^2)))*X^4 + C (c+d*(1+a^2))*X^3 +
      C (d*(d+1)+c*(1+b^2)+e*(1+a^2))*X^2 +
      C (e+d*(1+b^2))*X + C (e*(e+(1+b^2))) := by
  unfold k4QA k4QB k4QP
  simp only [map_add, map_mul, map_pow, map_one]
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero (Polynomial K) 2
  ring_nf
  simp [h2]

/-- The polynomial identities forced by a quadratic factorization are inconsistent. -/
theorem k4H_quadratic_equations_impossible (a b c d e : K)
    (hA : k4QA K a b * (k4QP K + (k4QA K a b)^2) = X * (X+1))
    (hB : k4QB K c d e * (k4QB K c d e + k4QP K + (k4QA K a b)^2) = (k4QP K)^2) : False := by
  have hA' : k4QA K a b * (k4QP K + (k4QA K a b)^2) = X^2 + X := by
    rw [hA]
    ring
  have hP : (k4QP K)^2 = (X^4 + X^2 + 1 : Polynomial K) := by
    unfold k4QP
    have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero (Polynomial K) 2
    have h3 : (3 : Polynomial K) = 1 := by linear_combination h2
    ring_nf
    simp [h2, h3]
  rw [k4QA_eqn_normal] at hA'
  rw [k4QB_eqn_normal, hP] at hB
  have ha : a^3+a = 0 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 3) hA'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hb : b^3+b = 0 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 0) hA'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hmix : a+b+a^2*b = 1 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 2) hA'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hc4 : c*(c+(1+a^2)) = 1 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 4) hB
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at ht
    norm_num at ht
    exact ht
  have hc3 : c+d*(1+a^2)=0 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 3) hB
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at ht
    norm_num at ht
    exact ht
  have he4 : e*(e+(1+b^2)) = 1 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 0) hB
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at ht
    norm_num at ht
    exact ht
  have he3 : e+d*(1+b^2)=0 := by
    have ht := congrArg (fun p : Polynomial K => p.coeff 1) hB
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at ht
    norm_num at ht
    exact ht
  exact k4H_quadratic_coefficient_obstruction K a b c d e ha hb hmix hc4 hc3 he4 he3

def k4HQuartic : Polynomial (Polynomial K) :=
  X^4 + C (k4QP K) * X^2 + C ((X : Polynomial K) * (X+1)) * X + C ((k4QP K)^2)

theorem k4H_quadratic_product_normal (a b c d e : K) (D : Polynomial K) :
    (X^2 + C (k4QA K a b)*X + C (k4QB K c d e)) *
      (X^2 + C (k4QA K a b)*X + C D) =
      (X^4 + C (k4QB K c d e + D + (k4QA K a b)^2)*X^2 +
       C (k4QA K a b * (k4QB K c d e + D))*X + C (k4QB K c d e * D) :
         Polynomial (Polynomial K)) := by
  simp only [map_add, map_mul, map_pow]
  have h2 : (2 : Polynomial (Polynomial K)) = 0 := CharP.cast_eq_zero _ 2
  ring_nf
  simp [h2]

theorem k4H_no_monic_homogeneous_quadratic_factorization
    (a b c d e : K) (D : Polynomial K)
    (hf : k4HQuartic K =
      (X^2 + C (k4QA K a b)*X + C (k4QB K c d e)) *
      (X^2 + C (k4QA K a b)*X + C D)) : False := by
  rw [k4H_quadratic_product_normal] at hf
  unfold k4HQuartic at hf
  have hsum : k4QB K c d e + D + (k4QA K a b)^2 = k4QP K := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 2) hf.symm
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hlinear : k4QA K a b * (k4QB K c d e + D) = (X : Polynomial K)*(X+1) := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 1) hf.symm
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have hconstant : k4QB K c d e * D = (k4QP K)^2 := by
    have ht := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 0) hf.symm
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at ht
    norm_num at ht
    exact ht
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero _ 2
  have hsum' : k4QB K c d e + D = k4QP K + (k4QA K a b)^2 := by
    linear_combination hsum - (k4QA K a b)^2*h2
  have hD : D = k4QB K c d e + k4QP K + (k4QA K a b)^2 := by
    linear_combination hsum' - (k4QB K c d e)*h2
  apply k4H_quadratic_equations_impossible K a b c d e
  · simpa [hsum'] using hlinear
  · simpa [hD] using hconstant

#print axioms k4H_no_monic_homogeneous_quadratic_factorization
#print axioms k4H_quadratic_equations_impossible
#print axioms k4QA_eqn_normal
#print axioms k4QB_eqn_normal
end Carlet
