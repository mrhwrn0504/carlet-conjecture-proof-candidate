import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable {R : Type*} [CommRing R]

theorem monic_degree_one_form (p : Polynomial R) (hp : p.Monic) (hd : p.natDegree = 1) :
    p = X + C (p.coeff 0) := by
  have htop : p.coeff 1 = 1 := by rw [← hd, Polynomial.coeff_natDegree]; exact hp.leadingCoeff
  ext n
  by_cases h0 : n = 0
  · subst n; simp
  by_cases h1 : n = 1
  · subst n; simp [htop]
  · have hn : p.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    have h1' : 1 ≠ n := Ne.symm h1
    simp [h0, h1']

theorem monic_degree_two_form (p : Polynomial R) (hp : p.Monic) (hd : p.natDegree = 2) :
    p = X^2 + C (p.coeff 1)*X + C (p.coeff 0) := by
  have htop : p.coeff 2 = 1 := by rw [← hd, Polynomial.coeff_natDegree]; exact hp.leadingCoeff
  ext n
  by_cases h0 : n = 0
  · subst n; simp
  by_cases h1 : n = 1
  · subst n; simp
  by_cases h2 : n = 2
  · subst n; simp [htop]
  · have hn : p.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    have h1' : 1 ≠ n := Ne.symm h1
    simp [h0, h1', h2]

#print axioms monic_degree_one_form
#print axioms monic_degree_two_form
end Carlet

