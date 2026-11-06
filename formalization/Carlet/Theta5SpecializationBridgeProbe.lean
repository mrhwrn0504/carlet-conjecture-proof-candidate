import Carlet.Theta5PositiveRecurrenceWordProbe
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

noncomputable section
namespace Carlet
open Polynomial MvPolynomial

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

def theta5SpecialHom (x : Fin 5 → K) : T5EvalRing →+* K :=
  MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K) x

def theta5SpecialP4 (x : Fin 5 → K) : Polynomial K :=
  t5EvalP4.map (theta5SpecialHom x)

lemma theta5SpecialHom_X (x : Fin 5 → K) (i : Fin 5) :
    theta5SpecialHom x (t5EvalX i) = x i := by
  simp [theta5SpecialHom, t5EvalX]

lemma theta5_map_eval (x : Fin 5 → K) (p : Polynomial T5EvalRing)
    (a : T5EvalRing) :
    theta5SpecialHom x (p.eval a) =
      (p.map (theta5SpecialHom x)).eval (theta5SpecialHom x a) := by
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map]

theorem theta5_specialize_coeff_identity (x : Fin 5 → K) :
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) =
      (theta5SpecialP4 x).coeff 8 ^ 2 + (theta5SpecialP4 x).eval (x 4) := by
  let φ := theta5SpecialHom x
  have hl : φ theta5 = MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) := by
    change MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x theta5 = _
    rw [MvPolynomial.eval₂_eq_eval_map]
  have hr : φ (t5EvalP4.eval (t5EvalX 4)) =
      (t5EvalP4.map φ).eval (x 4) := by
    rw [theta5_map_eval, theta5SpecialHom_X]
  have h := congrArg φ theta5_eq_coeff8_sq_add_eval
  change φ theta5 = φ ((t5EvalP4.coeff 8) ^ 2 +
    t5EvalP4.eval (t5EvalX 4)) at h
  rw [map_add, map_pow] at h
  calc
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = φ theta5 := hl.symm
    _ = φ (t5EvalP4.coeff 8) ^ 2 + φ (t5EvalP4.eval (t5EvalX 4)) := h
    _ = (t5EvalP4.map φ).coeff 8 ^ 2 + (t5EvalP4.map φ).eval (x 4) := by
      rw [← Polynomial.coeff_map, hr]
    _ = _ := rfl

#print axioms theta5_specialize_coeff_identity

end Carlet
