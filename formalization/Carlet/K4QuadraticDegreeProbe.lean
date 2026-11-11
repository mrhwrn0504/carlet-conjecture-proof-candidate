import Carlet.K4HQuadraticExtractionProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K]

theorem k4QP_degree : (k4QP K).natDegree = 2 := by
  unfold k4QP
  compute_degree; simp

theorem k4X_mul_X_add_one_degree : ((X : Polynomial K) * (X+1)).natDegree = 2 := by
  compute_degree; simp

theorem k4Quadratic_A_degree_le_one (A : Polynomial K)
    (h : A * (k4QP K + A^2) = X*(X+1)) : A.natDegree ≤ 1 := by
  have hr : (X : Polynomial K)*(X+1) ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    rw [k4X_mul_X_add_one_degree] at hd
    simp at hd
  have ha : A ≠ 0 := by
    intro hz
    apply hr
    simpa [hz] using h.symm
  have hb : k4QP K + A^2 ≠ 0 := by
    intro hz
    apply hr
    simpa [hz] using h.symm
  by_contra hn
  have hlarge : 1 < A.natDegree := by omega
  have hless : (k4QP K).natDegree < (A^2).natDegree := by
    rw [k4QP_degree, Polynomial.natDegree_pow]
    omega
  have hsum : (k4QP K + A^2).natDegree = 2*A.natDegree := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hless, Polynomial.natDegree_pow]
  have hm := Polynomial.natDegree_mul ha hb
  rw [h, k4X_mul_X_add_one_degree, hsum] at hm
  omega

theorem k4Quadratic_B_degree_le_two (A B D : Polynomial K)
    (hA : A.natDegree ≤ 1)
    (hs : B+D = k4QP K + A^2)
    (hp : B*D = (k4QP K)^2) : B.natDegree ≤ 2 := by
  have hP : k4QP K ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    rw [k4QP_degree] at hd
    simp at hd
  have hp2 : (k4QP K)^2 ≠ 0 := pow_ne_zero 2 hP
  have hB : B ≠ 0 := by
    intro hz
    apply hp2
    simpa [hz] using hp.symm
  have hD : D ≠ 0 := by
    intro hz
    apply hp2
    simpa [hz] using hp.symm
  have hsum : (B+D).natDegree ≤ 2 := by
    rw [hs]
    have hpdeg : (k4QP K).natDegree ≤ 2 := by rw [k4QP_degree]
    have hadeg : (A^2).natDegree ≤ 2 := by
      rw [Polynomial.natDegree_pow]
      omega
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hpdeg hadeg)
  have hm := Polynomial.natDegree_mul hB hD
  rw [hp, Polynomial.natDegree_pow, k4QP_degree] at hm
  by_contra hn
  have hlt : D.natDegree < B.natDegree := by omega
  have heq := Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
  omega

#print axioms k4Quadratic_B_degree_le_two
#print axioms k4Quadratic_A_degree_le_one
end Carlet

