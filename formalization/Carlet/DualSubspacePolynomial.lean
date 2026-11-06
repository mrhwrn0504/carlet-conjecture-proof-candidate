import Carlet.DualCoefficients

noncomputable section

open Polynomial
open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

def subspaceFrobeniusCoefficients (E : Submodule (ZMod 2) K) (i : ℕ) : K :=
  (rootProduct (underlyingFinset E)).coeff (2^i)

theorem subspaceFrobeniusCoefficients_zero_ne (E : Submodule (ZMod 2) K) :
    subspaceFrobeniusCoefficients E 0 ≠ 0 := by
  simpa only [subspaceFrobeniusCoefficients, pow_zero] using
    rootProduct_coeff_one_ne (underlyingFinset E) (by simp)

theorem dualSubspace_polynomial (E : Submodule (ZMod 2) K) :
    normalizedDualPolynomial (subspaceFrobeniusCoefficients E) (Module.finrank (ZMod 2) E) =
      rootProduct (underlyingFinset (dualImageEquiv E)) := by
  apply monic_eq_rootProduct
  · exact normalizedDualPolynomial_monic _ _ (subspaceFrobeniusCoefficients_zero_ne E)
  · rw [normalizedDualPolynomial_natDegree _ _ (subspaceFrobeniusCoefficients_zero_ne E),
      underlyingFinset_card_pow, dualImage_finrank]
  · intro y hy
    rw [normalizedDualPolynomial, eval_mul, eval_C]
    have h := (subspaceDualPolynomial_eval_zero_iff E y).mpr
      ((mem_underlyingFinset (dualImageEquiv E) y).mp hy)
    change (dualPolynomial (subspaceFrobeniusCoefficients E) (Module.finrank (ZMod 2) E)).eval y = 0 at h
    rw [h, mul_zero]

theorem dualSubspace_coeff_one (E : Submodule (ZMod 2) K) :
    (rootProduct (underlyingFinset (dualImageEquiv E))).coeff 1 =
      ((rootProduct (underlyingFinset E)).coeff 1 ^ (2^Module.finrank (ZMod 2) E))⁻¹ := by
  rw [← dualSubspace_polynomial]
  have h := normalizedDualPolynomial_coeff (subspaceFrobeniusCoefficients E)
    (Module.finrank (ZMod 2) E) 0 (Nat.zero_le _)
  simp only [pow_zero, Nat.sub_zero, pow_one, subspaceFrobeniusCoefficients] at h
  have hl : (rootProduct (underlyingFinset E)).coeff (2^Module.finrank (ZMod 2) E) = 1 := by
    rw [← subspacePolynomial_natDegree_pow]
    exact (rootProduct_monic _).coeff_natDegree
  simpa only [hl, mul_one] using h

theorem dualSubspace_coeff_two (E : Submodule (ZMod 2) K)
    (hd : 0 < Module.finrank (ZMod 2) E) :
    (rootProduct (underlyingFinset (dualImageEquiv E))).coeff 2 =
      ((rootProduct (underlyingFinset E)).coeff 1 ^ (2^Module.finrank (ZMod 2) E))⁻¹ *
        nextFrobeniusCoefficient E ^ 2 := by
  rw [← dualSubspace_polynomial]
  have h := normalizedDualPolynomial_coeff (subspaceFrobeniusCoefficients E)
    (Module.finrank (ZMod 2) E) 1 hd
  simpa only [pow_zero, pow_one, subspaceFrobeniusCoefficients, nextFrobeniusCoefficient] using h

theorem inverse_sum_dualImage (E : Submodule (ZMod 2) K)
    (hd : 0 < Module.finrank (ZMod 2) E) :
    (∑ x ∈ (underlyingFinset (dualImageEquiv E)).erase 0, x⁻¹) =
      nextFrobeniusCoefficient E ^ 2 := by
  rw [inverse_sum_eq_rootProduct_coeff_ratio _ (by simp),
    dualSubspace_coeff_two E hd, dualSubspace_coeff_one]
  exact mul_div_cancel_left₀ _ (inv_ne_zero (pow_ne_zero _
    (rootProduct_coeff_one_ne (underlyingFinset E) (by simp))))

theorem zeroSum_dualImage_iff (E : Submodule (ZMod 2) K)
    (hd : 0 < Module.finrank (ZMod 2) E) :
    IsZeroSum (dualImageEquiv E) ↔ nextFrobeniusCoefficient E = 0 := by
  rw [zeroSum_iff_coeff_two, dualSubspace_coeff_two E hd, mul_eq_zero]
  have h := inv_ne_zero (pow_ne_zero (2^Module.finrank (ZMod 2) E)
    (rootProduct_coeff_one_ne (underlyingFinset E) (by simp)))
  simp only [h, false_or, sq_eq_zero_iff]

def nextCoefficientZeroEquivZeroSum (k : ℕ) (hk : 0 < k) :
    {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧
      nextFrobeniusCoefficient E = 0} ≃
    {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧ IsZeroSum E} :=
  dualImageEquiv.subtypeEquiv (fun E => by
    rw [dualImage_finrank]
    constructor
    · rintro ⟨hr,ht⟩
      exact ⟨hr, (zeroSum_dualImage_iff E (by omega)).mpr ht⟩
    · rintro ⟨hr,ht⟩
      exact ⟨hr, (zeroSum_dualImage_iff E (by omega)).mp ht⟩)

theorem nextCoefficientZero_count (k : ℕ) (hk : 0 < k) :
    Nat.card {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧
      nextFrobeniusCoefficient E = 0} =
    Nat.card {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧ IsZeroSum E} :=
  Nat.card_congr (nextCoefficientZeroEquivZeroSum k hk)

#print axioms dualSubspace_polynomial
#print axioms dualSubspace_coeff_two
#print axioms inverse_sum_dualImage
#print axioms nextCoefficientZero_count

end Carlet
