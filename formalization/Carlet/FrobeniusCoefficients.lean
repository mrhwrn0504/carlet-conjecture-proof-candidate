import Carlet.SubspaceSupport

noncomputable section

open Polynomial
open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K]

theorem frobeniusSupported_eq_sum (p : K[X]) (hp : FrobeniusSupported p) (d : ℕ)
    (hd : p.natDegree ≤ 2^d) :
    p = ∑ j ∈ Finset.range (d+1), monomial (2^j) (p.coeff (2^j)) := by
  classical
  ext k
  rw [finsetSum_coeff]
  by_cases hk : p.coeff k = 0
  · rw [hk]
    symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : 2^j = k
    · simp [hj, hk]
    · simp [coeff_monomial, hj]
  · obtain ⟨j,rfl⟩ := hp k hk
    have hj : j ∈ Finset.range (d+1) := by
      apply Finset.mem_range.mpr
      have hpow := (Polynomial.le_natDegree_of_ne_zero hk).trans hd
      have hle := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
      omega
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      have hi : 2^i ≠ 2^j := fun h => hij (Nat.pow_right_injective (by decide) h)
      simp [coeff_monomial, hi]
    · exact fun h => False.elim (h hj)

variable [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem artinSchreier_pow (j : ℕ) :
    ((X^2+X : K[X])^(2^j)) = X^(2^(j+1))+X^(2^j) := by
  rw [add_pow_char_pow _ _ 2, ← pow_mul]
  simp only [pow_succ, Nat.mul_comm]

theorem coeff_comp_artinSchreier (p : K[X]) (hp : FrobeniusSupported p) (d : ℕ)
    (hd : p.natDegree ≤ 2^d) (hd0 : 0 < d) :
    (p.comp (X^2+X)).coeff (2^d) = p.coeff (2^(d-1)) + p.coeff (2^d) := by
  classical
  conv_lhs => rw [frobeniusSupported_eq_sum p hp d hd]
  simp only [sum_comp, monomial_comp, finsetSum_coeff, coeff_C_mul,
    artinSchreier_pow, coeff_add, coeff_X_pow]
  have hpow (i j : ℕ) : (2^i = 2^j) ↔ i = j :=
    (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff
  have hprev (j : ℕ) : d = j+1 ↔ j = d-1 := by omega
  simp only [hpow, hprev, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  simp [show d-1 < d+1 by omega]

#print axioms frobeniusSupported_eq_sum
#print axioms coeff_comp_artinSchreier

end Carlet
