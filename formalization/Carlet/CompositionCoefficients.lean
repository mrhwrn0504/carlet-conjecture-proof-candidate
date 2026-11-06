import Carlet.Elementary
import Mathlib.Algebra.Polynomial.Div

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K]

theorem coeff_pow_eq_zero_of_lt (q : K[X]) (hq : q.coeff 0 = 0) (n j : ℕ)
    (hjn : j < n) : (q ^ n).coeff j = 0 := by
  obtain ⟨r, rfl⟩ := Polynomial.X_dvd_iff.mpr hq
  rw [mul_pow, Polynomial.coeff_X_pow_mul']
  simp [not_le_of_gt hjn]

theorem coeff_comp_one (p q : K[X]) (hq : q.coeff 0 = 0) :
    (p.comp q).coeff 1 = p.coeff 1 * q.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [add_comp, coeff_add, hp, hr]; ring
  | monomial n a =>
    by_cases h0 : n = 0
    · subst n
      simp
    by_cases h1 : n = 1
    · subst n
      simp [monomial_comp]
    have hn : 1 < n := by omega
    simp [monomial_comp, coeff_monomial, h1,
      coeff_pow_eq_zero_of_lt q hq n 1 hn]

theorem coeff_comp_two (p q : K[X]) (hq : q.coeff 0 = 0) :
    (p.comp q).coeff 2 = p.coeff 1 * q.coeff 2 + p.coeff 2 * q.coeff 1 ^ 2 := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [add_comp, coeff_add, hp, hr]; ring
  | monomial n a =>
    by_cases h0 : n = 0
    · subst n
      simp
    by_cases h1 : n = 1
    · subst n
      simp [monomial_comp, coeff_monomial]
    by_cases h2 : n = 2
    · subst n
      have hs : (q ^ 2).coeff 2 = q.coeff 1 ^ 2 := by
        simpa using extension_coeff_two q 0 hq
      simp [monomial_comp, coeff_monomial, hs]
    have hn : 2 < n := by omega
    simp [monomial_comp, coeff_monomial, h1, h2,
      coeff_pow_eq_zero_of_lt q hq n 2 hn]

#print axioms coeff_comp_one
#print axioms coeff_comp_two

end Carlet
