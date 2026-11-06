import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet

/-- In a domain, a polynomial with nonzero constant coefficient that divides a
    nonzero monomial is constant. -/
theorem polynomial_factor_of_monomial_constant {R : Type*} [CommRing R] [IsDomain R]
    (n : ℕ) (f g : Polynomial R) (a : R) (ha : a ≠ 0) (hf : f.coeff 0 ≠ 0)
    (hfg : f*g = C a * X^n) : f = C (f.coeff 0) := by
  induction n generalizing g with
  | zero =>
    have hfg' : f*g = C a := by simpa using hfg
    have hf0 : f ≠ 0 := by intro hz; apply hf; simp [hz]
    have hg0 : g ≠ 0 := by
      intro hz
      have hc : (C a : Polynomial R) = 0 := by simpa [hz] using hfg'.symm
      exact (Polynomial.C_ne_zero.mpr ha) hc
    have hd := Polynomial.natDegree_mul hf0 hg0
    rw [hfg', Polynomial.natDegree_C] at hd
    have hfd : f.natDegree = 0 := by omega
    exact Polynomial.eq_C_of_natDegree_eq_zero hfd
  | succ n ih =>
    have hgcoeff : g.coeff 0 = 0 := by
      have hc := congrArg (fun p : Polynomial R => p.coeff 0) hfg
      simp [Polynomial.coeff_mul] at hc
      exact hc.resolve_left hf
    obtain ⟨g', hg'⟩ := Polynomial.X_dvd_iff.mpr hgcoeff
    have hcancel : f*g' = C a * X^n := by
      apply mul_right_cancel₀ (Polynomial.X_ne_zero : (X : Polynomial R) ≠ 0)
      calc
        (f*g')*X = f*(X*g') := by ring
        _ = f*g := by rw [hg']
        _ = C a * X^(n+1) := hfg
        _ = (C a * X^n)*X := by rw [pow_succ]; ring
    exact ih g' hcancel

#print axioms polynomial_factor_of_monomial_constant
end Carlet
