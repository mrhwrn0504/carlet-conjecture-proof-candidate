import Carlet.K4QuadraticDegreeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K]

theorem k4Polynomial_normal_linear (A : Polynomial K) (hA : A.natDegree ≤ 1) :
    A = k4QA K (A.coeff 1) (A.coeff 0) := by
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [k4QA]
  by_cases h1 : n = 1
  · subst n
    simp [k4QA]
  · have hn : A.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    simp only [k4QA, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    have h1' : 1 ≠ n := Ne.symm h1
    simp [h0, h1']

theorem k4Polynomial_normal_quadratic (B : Polynomial K) (hB : B.natDegree ≤ 2) :
    B = k4QB K (B.coeff 2) (B.coeff 1) (B.coeff 0) := by
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [k4QB]
  by_cases h1 : n = 1
  · subst n
    simp [k4QB]
  by_cases h2 : n = 2
  · subst n
    simp [k4QB]
  · have hn : B.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    simp only [k4QB, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    have h1' : 1 ≠ n := Ne.symm h1
    simp [h0, h1', h2]

#print axioms k4Polynomial_normal_linear
#print axioms k4Polynomial_normal_quadratic
end Carlet
