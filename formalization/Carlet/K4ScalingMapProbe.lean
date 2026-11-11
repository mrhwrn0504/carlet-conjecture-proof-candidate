import Carlet.K4ScalingMonomialFactorProbe
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable {σ K : Type*} [Field K]
abbrev ScaleBase (σ K : Type*) [Field K] := MvPolynomial σ K

def k4Scale : MvPolynomial σ K →+* Polynomial (ScaleBase σ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

theorem k4Scale_eval_one (f : MvPolynomial σ K) : (k4Scale f).eval 1 = f := by
  have he : (Polynomial.evalRingHom 1).comp (k4Scale : MvPolynomial σ K →+* Polynomial (ScaleBase σ K)) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [k4Scale, MvPolynomial.eval₂Hom]
    · intro i
      simp [k4Scale, MvPolynomial.eval₂Hom]
  exact DFunLike.congr_fun he f

theorem k4Scale_coeff_zero (f : MvPolynomial σ K) :
    (k4Scale f).coeff 0 = MvPolynomial.C (MvPolynomial.eval (fun _ => 0) f) := by
  have he : (Polynomial.constantCoeff).comp (k4Scale : MvPolynomial σ K →+* Polynomial (ScaleBase σ K)) =
      MvPolynomial.C.comp (MvPolynomial.eval (fun _ => 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [k4Scale, MvPolynomial.eval₂Hom]
    · intro i
      simp [k4Scale, MvPolynomial.eval₂Hom]
  exact DFunLike.congr_fun he f

/-- A factor with nonzero value at the origin of a polynomial satisfying
    the scaling identity is a unit. -/
theorem k4Scale_factor_unit (p f g : MvPolynomial σ K) (n : ℕ)
    (hp : p ≠ 0) (hscale : k4Scale p = Polynomial.C p * Polynomial.X^n)
    (hfg : p = f*g) (hforigin : MvPolynomial.eval (fun _ => 0) f ≠ 0) : IsUnit f := by
  have hsprod : k4Scale f * k4Scale g = Polynomial.C p * Polynomial.X^n := by
    rw [← map_mul, ← hfg, hscale]
  have hfzero : (k4Scale f).coeff 0 ≠ 0 := by
    rw [k4Scale_coeff_zero]
    exact MvPolynomial.C_ne_zero.mpr hforigin
  have hconstant := polynomial_factor_of_monomial_constant n (k4Scale f) (k4Scale g) p hp hfzero hsprod
  have heval := congrArg (Polynomial.eval 1) hconstant
  rw [k4Scale_eval_one, k4Scale_coeff_zero] at heval
  simp only [Polynomial.eval_C] at heval
  rw [heval]
  exact (isUnit_iff_ne_zero.mpr hforigin).map MvPolynomial.C

#print axioms k4Scale_factor_unit
#print axioms k4Scale_eval_one
#print axioms k4Scale_coeff_zero
end Carlet
