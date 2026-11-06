import Carlet.DualSubspacePolynomial
import Mathlib.Tactic

noncomputable section
namespace Carlet
open Polynomial

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
  [DecidableEq K]

/-- In dimension four the next-to-leading subspace coefficient is the
    coefficient of X^8.  It controls the zero sum of the dual-image space. -/
theorem zeroSum_dualImage_iff_coeff8 (E : Submodule (ZMod 2) K)
    (hE : Module.finrank (ZMod 2) E = 4) :
    IsZeroSum (dualImageEquiv E) ↔
      (rootProduct (underlyingFinset E)).coeff 8 = 0 := by
  rw [zeroSum_dualImage_iff E (by rw [hE]; omega)]
  unfold nextFrobeniusCoefficient
  rw [hE]
  norm_num

/-- The rank-four existence problem is equivalent to finding a rank-four
    subspace whose subspace polynomial has vanishing X^8 coefficient. -/
theorem hasZeroSumSubspace_four_iff_exists_coeff8 :
    HasZeroSumSubspace K 4 ↔
      ∃ E : Submodule (ZMod 2) K,
        Module.finrank (ZMod 2) E = 4 ∧
          (rootProduct (underlyingFinset E)).coeff 8 = 0 := by
  constructor
  · rintro ⟨V, hV, hzero⟩
    let E := (dualImageEquiv (K := K)).symm V
    have hE : Module.finrank (ZMod 2) E = 4 := by
      calc
        Module.finrank (ZMod 2) E =
            Module.finrank (ZMod 2) (dualImageEquiv E) := by rw [dualImage_finrank]
        _ = Module.finrank (ZMod 2) V := by
          rw [show dualImageEquiv E = V from Equiv.apply_symm_apply _ _]
        _ = 4 := hV
    refine ⟨E, hE, ?_⟩
    have hiff := zeroSum_dualImage_iff_coeff8 E hE
    rw [show dualImageEquiv E = V from Equiv.apply_symm_apply _ _] at hiff
    exact hiff.mp hzero
  · rintro ⟨E, hE, hcoeff⟩
    refine ⟨dualImageEquiv E, ?_, ?_⟩
    · rw [dualImage_finrank, hE]
    · exact (zeroSum_dualImage_iff_coeff8 E hE).mpr hcoeff

#print axioms zeroSum_dualImage_iff_coeff8
#print axioms hasZeroSumSubspace_four_iff_exists_coeff8
end Carlet
