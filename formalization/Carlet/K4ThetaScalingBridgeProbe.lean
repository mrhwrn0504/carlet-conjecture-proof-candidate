import Carlet.K4ThetaScalingProbe
import Carlet.K4ThetaConstantUnitProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

def k4ThetaEquivOver : MvPolynomial (Fin 4) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 4) 3)).trans (MvPolynomial.finSuccEquiv K 3)

lemma k4FinSuccC {R : Type*} [CommSemiring R] (r : R) :
    (MvPolynomial.finSuccEquiv R 3) (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  exact (MvPolynomial.finSuccEquiv R 3).commutes r

lemma k4FinSuccX1 {R : Type*} [CommSemiring R] :
    (MvPolynomial.finSuccEquiv R 3) (MvPolynomial.X (1 : Fin 4)) = Polynomial.C (MvPolynomial.X (0 : Fin 3)) := by
  simpa using (MvPolynomial.finSuccEquiv_X_succ (R := R) (n := 3) (j := (0 : Fin 3)))
lemma k4FinSuccX2 {R : Type*} [CommSemiring R] :
    (MvPolynomial.finSuccEquiv R 3) (MvPolynomial.X (2 : Fin 4)) = Polynomial.C (MvPolynomial.X (1 : Fin 3)) := by
  simpa using (MvPolynomial.finSuccEquiv_X_succ (R := R) (n := 3) (j := (1 : Fin 3)))
lemma k4FinSuccX3 {R : Type*} [CommSemiring R] :
    (MvPolynomial.finSuccEquiv R 3) (MvPolynomial.X (3 : Fin 4)) = Polynomial.C (MvPolynomial.X (2 : Fin 3)) := by
  simpa using (MvPolynomial.finSuccEquiv_X_succ (R := R) (n := 3) (j := (2 : Fin 3)))

omit [Algebra (ZMod 2) K] in
theorem k4ThetaEquivOver_origin (f : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (fun _ => 0) ((k4ThetaEquivOver K f).coeff 0) =
      MvPolynomial.eval (fun _ => 0) f := by
  have he : (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))).comp
      (Polynomial.constantCoeff.comp (k4ThetaEquivOver K).toRingEquiv.toRingHom) =
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [k4ThetaEquivOver, MvPolynomial.renameEquiv, k4FinSuccC]
    · intro i
      fin_cases i <;> simp [k4ThetaEquivOver, MvPolynomial.renameEquiv,
        MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero,
        k4FinSuccX1, k4FinSuccX2, k4FinSuccX3, Equiv.swap_apply_def]
  exact DFunLike.congr_fun he f

theorem k4ThetaEquivOver_basechange : k4ThetaEquivOver K (k4ThetaOver K) = k4ThetaPolyOver K := by
  have he : (k4ThetaEquivOver K).toRingEquiv.toRingHom.comp
      (MvPolynomial.map (algebraMap (ZMod 2) K)) =
      (Polynomial.mapRingHom (MvPolynomial.map (algebraMap (ZMod 2) K))).comp
        theta4PolynomialEquiv.toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [k4ThetaEquivOver, theta4PolynomialEquiv, MvPolynomial.renameEquiv, k4FinSuccC]
    · intro i
      fin_cases i <;> simp [k4ThetaEquivOver, theta4PolynomialEquiv, MvPolynomial.renameEquiv,
        MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero,
        k4FinSuccX1, k4FinSuccX2, k4FinSuccX3, Equiv.swap_apply_def]
  exact DFunLike.congr_fun he theta4

#print axioms k4ThetaEquivOver_origin
#print axioms k4ThetaEquivOver_basechange
end Carlet

