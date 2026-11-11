import Carlet.K4ThetaScalingBridgeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

theorem k4ThetaOver_eval_origin : MvPolynomial.eval (fun _ : Fin 4 => (0 : K)) (k4ThetaOver K) = 0 := by
  simp [k4ThetaOver, theta4, k4X]

theorem k4ThetaOver_ne_zero : k4ThetaOver K ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval (![1,0,0,0] : Fin 4 → K)) hz
  simp [k4ThetaOver, theta4, k4X] at he

theorem k4ThetaOver_not_unit : ¬ IsUnit (k4ThetaOver K) := by
  intro hu
  have h := hu.map (MvPolynomial.eval (fun _ : Fin 4 => (0 : K)))
  rw [k4ThetaOver_eval_origin] at h
  exact h.ne_zero rfl

/-- The actual Θ₄ remains irreducible after extending scalars to any field of
    characteristic two. -/
theorem k4ThetaOver_irreducible : Irreducible (k4ThetaOver K) := by
  rw [irreducible_iff]
  refine ⟨k4ThetaOver_not_unit K, ?_⟩
  intro f g hfg
  have hfactors : k4ThetaPolyOver K = k4ThetaEquivOver K f * k4ThetaEquivOver K g := by
    rw [← k4ThetaEquivOver_basechange, hfg, map_mul]
  rcases k4Theta_factors_constant_unit K _ _ hfactors with hf | hg
  · left
    have hv : IsUnit (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))
        ((k4ThetaEquivOver K f).coeff 0)) :=
      hf.map (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))
    have hforigin : MvPolynomial.eval (fun _ : Fin 4 => (0 : K)) f ≠ 0 := by
      rw [← k4ThetaEquivOver_origin K f]
      exact hv.ne_zero
    exact k4Scale_factor_unit (k4ThetaOver K) f g 8 (k4ThetaOver_ne_zero K)
      (k4ThetaOver_scaling K) hfg hforigin
  · right
    have hv : IsUnit (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))
        ((k4ThetaEquivOver K g).coeff 0)) :=
      hg.map (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))
    have hgorigin : MvPolynomial.eval (fun _ : Fin 4 => (0 : K)) g ≠ 0 := by
      rw [← k4ThetaEquivOver_origin K g]
      exact hv.ne_zero
    exact k4Scale_factor_unit (k4ThetaOver K) g f 8 (k4ThetaOver_ne_zero K)
      (k4ThetaOver_scaling K) (by simpa [mul_comm] using hfg) hgorigin

#print axioms k4ThetaOver_eval_origin
#print axioms k4ThetaOver_ne_zero
#print axioms k4ThetaOver_not_unit
#print axioms k4ThetaOver_irreducible
end Carlet
