import Carlet.DualPolynomial
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section

open Polynomial
open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K]

theorem dualPolynomial_reversed (c : ℕ → K) (d : ℕ) :
    dualPolynomial c d =
      ∑ j ∈ Finset.range (d+1), C ((c (d-j))^(2^j))*X^(2^j) := by
  rw [dualPolynomial, ← Finset.sum_range_reflect
    (fun i => C ((c i)^(2^(d-i)))*X^(2^(d-i))) (d+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have h : d-(d-j)=j := by have := Finset.mem_range.mp hj; omega
  simp only [Nat.add_sub_cancel, h]

theorem dualPolynomial_coeff (c : ℕ → K) (d j : ℕ) (hj : j ≤ d) :
    (dualPolynomial c d).coeff (2^j) = (c (d-j))^(2^j) := by
  classical
  rw [dualPolynomial_reversed, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  have hpow (i k : ℕ) : (2^i = 2^k) ↔ i = k :=
    (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff
  simp only [hpow, mul_ite, mul_one, mul_zero]
  simp [show j < d+1 by omega]

theorem dualPolynomial_natDegree_le (c : ℕ → K) (d : ℕ) :
    (dualPolynomial c d).natDegree ≤ 2^d := by
  rw [dualPolynomial_reversed]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_X_pow_le _ _).trans
  exact Nat.pow_le_pow_right (by decide) (by have := Finset.mem_range.mp hj; omega)

theorem dualPolynomial_natDegree (c : ℕ → K) (d : ℕ) (hc : c 0 ≠ 0) :
    (dualPolynomial c d).natDegree = 2^d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (dualPolynomial_natDegree_le c d)
  rw [dualPolynomial_coeff c d d le_rfl, Nat.sub_self]
  exact pow_ne_zero _ hc

def normalizedDualPolynomial (c : ℕ → K) (d : ℕ) : K[X] :=
  C ((c 0)^(2^d))⁻¹ * dualPolynomial c d

theorem normalizedDualPolynomial_monic (c : ℕ → K) (d : ℕ) (hc : c 0 ≠ 0) :
    (normalizedDualPolynomial c d).Monic := by
  have hl : (dualPolynomial c d).leadingCoeff = (c 0)^(2^d) := by
    rw [leadingCoeff, dualPolynomial_natDegree c d hc, dualPolynomial_coeff c d d le_rfl,
      Nat.sub_self]
  have hp : dualPolynomial c d ≠ 0 := by
    intro h
    rw [h, leadingCoeff_zero] at hl
    exact (pow_ne_zero _ hc) hl.symm
  rw [normalizedDualPolynomial, mul_comm]
  simpa only [hl] using monic_mul_leadingCoeff_inv hp

theorem normalizedDualPolynomial_natDegree (c : ℕ → K) (d : ℕ) (hc : c 0 ≠ 0) :
    (normalizedDualPolynomial c d).natDegree = 2^d := by
  rw [normalizedDualPolynomial, natDegree_C_mul (inv_ne_zero (pow_ne_zero _ hc)),
    dualPolynomial_natDegree c d hc]

theorem normalizedDualPolynomial_coeff (c : ℕ → K) (d j : ℕ) (hj : j ≤ d) :
    (normalizedDualPolynomial c d).coeff (2^j) =
      ((c 0)^(2^d))⁻¹ * (c (d-j))^(2^j) := by
  rw [normalizedDualPolynomial, coeff_C_mul, dualPolynomial_coeff c d j hj]

#print axioms dualPolynomial_coeff
#print axioms dualPolynomial_natDegree
#print axioms normalizedDualPolynomial_monic

end Carlet
