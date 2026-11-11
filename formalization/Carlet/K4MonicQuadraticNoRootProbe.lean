import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

noncomputable section
namespace Carlet
open Polynomial

theorem monic_quadratic_irreducible_of_no_root
    {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : p.Monic) (hdeg : p.natDegree = 2)
    (hroot : ∀ x : R, p.eval x ≠ 0) : Irreducible p := by
  have hpne : p ≠ 1 := by
    intro h
    rw [h] at hdeg
    norm_num at hdeg
  rw [Polynomial.Monic.irreducible_iff_degree_lt hp hpne]
  intro q hqdeg hqdiv
  obtain ⟨r, hqr⟩ := hqdiv
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hdeg
    norm_num at hdeg
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hqr
    exact hp0 hqr
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hqr
    exact hp0 hqr
  have hqNat : q.natDegree ≤ 1 := by
    rw [hdeg] at hqdeg
    norm_num at hqdeg
    rw [Polynomial.degree_eq_natDegree hq0] at hqdeg
    exact_mod_cast hqdeg
  have hnatmul := Polynomial.natDegree_mul hq0 hr0
  rw [← hqr, hdeg] at hnatmul
  by_cases hqConst : q.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hqConst
    have hlc : q.leadingCoeff * r.leadingCoeff = 1 := by
      calc
        q.leadingCoeff * r.leadingCoeff = (q * r).leadingCoeff := by
          rw [Polynomial.leadingCoeff_mul]
        _ = p.leadingCoeff := by rw [hqr]
        _ = 1 := hp.leadingCoeff
    have hcUnit : IsUnit c := by
      apply (isUnit_iff_exists_inv).2
      refine ⟨r.leadingCoeff, ?_⟩
      rw [← hc, Polynomial.leadingCoeff_C] at hlc
      exact hlc
    rw [Polynomial.isUnit_iff]
    exact ⟨c, hcUnit, hc⟩
  · have hqNatEq : q.natDegree = 1 := by omega
    have hlc : q.leadingCoeff * r.leadingCoeff = 1 := by
      calc
        q.leadingCoeff * r.leadingCoeff = (q * r).leadingCoeff := by
          rw [Polynomial.leadingCoeff_mul]
        _ = p.leadingCoeff := by rw [hqr]
        _ = 1 := hp.leadingCoeff
    have hqForm : q = Polynomial.C q.leadingCoeff * Polynomial.X +
        Polynomial.C (q.coeff 0) := by
      apply Polynomial.ext
      intro n
      by_cases hn0 : n = 0
      · subst n
        simp
      · by_cases hn1 : n = 1
        · subst n
          rw [show q.coeff 1 = q.leadingCoeff by
            rw [← hqNatEq, Polynomial.coeff_natDegree]]
          simp
        · have hn2 : 2 ≤ n := by omega
          have hzero : q.coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hcx : (Polynomial.C q.leadingCoeff * Polynomial.X).coeff n = 0 := by
            rw [Polynomial.coeff_C_mul_X]
            simp [hn1]
          have hcc : (Polynomial.C (q.coeff 0)).coeff n = 0 := by
            rw [show n = (n - 1) + 1 by omega, Polynomial.coeff_C_succ]
          rw [Polynomial.coeff_add, hcx, hcc, hzero]
          simp
    let x : R := -(q.coeff 0 * r.leadingCoeff)
    have hqEval : q.eval x = 0 := by
      rw [hqForm, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
      dsimp [x]
      calc
        q.leadingCoeff * -(q.coeff 0 * r.leadingCoeff) + q.coeff 0 =
            -(q.coeff 0 * r.leadingCoeff) * q.leadingCoeff + q.coeff 0 := by ring
        _ =
            q.coeff 0 * (1 - r.leadingCoeff * q.leadingCoeff) := by ring
        _ = 0 := by
          rw [show r.leadingCoeff * q.leadingCoeff = 1 by simpa [mul_comm] using hlc]
          simp
    have hpEval : p.eval x = 0 := by
      rw [hqr, Polynomial.eval_mul, hqEval, zero_mul]
    exact (hroot x) hpEval |>.elim

#print axioms monic_quadratic_irreducible_of_no_root
end Carlet
