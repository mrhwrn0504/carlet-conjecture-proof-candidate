import Carlet.K4QuadraticDegreeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K]

theorem k4HQuartic_root_degree_le_one (A : Polynomial K)
    (h : A^4 + k4QP K*A^2 + (X : Polynomial K)*(X+1)*A + (k4QP K)^2 = 0) :
    A.natDegree ≤ 1 := by
  by_contra hn
  have hlarge : 1 < A.natDegree := by omega
  have h1 : (k4QP K * A^2).natDegree ≤ 2+2*A.natDegree := by
    have ht : (k4QP K * A^2).natDegree ≤ (k4QP K).natDegree + (A^2).natDegree := Polynomial.natDegree_mul_le
    rw [k4QP_degree, Polynomial.natDegree_pow] at ht
    exact ht
  have h2 : (((X : Polynomial K)*(X+1))*A).natDegree ≤ 2+A.natDegree := by
    have ht : (((X : Polynomial K)*(X+1))*A).natDegree ≤ ((X : Polynomial K)*(X+1)).natDegree + A.natDegree := Polynomial.natDegree_mul_le
    rw [k4X_mul_X_add_one_degree] at ht
    exact ht
  have h3 : ((k4QP K)^2).natDegree = 4 := by
    rw [Polynomial.natDegree_pow, k4QP_degree]
  have hb1 : (k4QP K * A^2).natDegree ≤ 2+2*A.natDegree := h1
  have hb2 : (((X : Polynomial K)*(X+1))*A).natDegree ≤ 2+2*A.natDegree := by omega
  have hb3 : ((k4QP K)^2).natDegree ≤ 2+2*A.natDegree := by omega
  have hb : (k4QP K*A^2 + (X : Polynomial K)*(X+1)*A + (k4QP K)^2).natDegree ≤
      2+2*A.natDegree := by
    apply le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ hb3)
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hb1 hb2)
  have heq : A^4 = -(k4QP K*A^2 + (X : Polynomial K)*(X+1)*A + (k4QP K)^2) := by
    linear_combination h
  have hd := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg] at hd
  omega

#print axioms k4HQuartic_root_degree_le_one
end Carlet
