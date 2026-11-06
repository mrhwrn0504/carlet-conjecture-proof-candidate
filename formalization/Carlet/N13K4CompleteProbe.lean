import Carlet.N13K4CodeEquivProbe
import Carlet.N13FieldBridgeProbe
import Carlet.Statement
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
namespace N13K4
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩

def subsetSum (s : Finset (Fin 4)) : AdjoinRoot f13 := ∑ i ∈ s, base i
theorem subsetSum_empty : subsetSum (∅ : Finset (Fin 4)) = 0 := by simp [subsetSum]
theorem subsetSum_injective : Function.Injective subsetSum := by
  intro s t h
  let gs := fun i : Fin 4 => if i ∈ s then (1 : F13) else 0
  let gt := fun i : Fin 4 => if i ∈ t then (1 : F13) else 0
  have hs : support gs = s := by ext i; simp [support, gs]
  have ht : support gt = t := by ext i; simp [support, gt]
  have hlin : (Fintype.linearCombination F13 base) gs = (Fintype.linearCombination F13 base) gt := by
    rw [Fintype.linearCombination_apply, support_sum, hs,
      Fintype.linearCombination_apply, support_sum, ht]
    exact h
  have hfun : gs = gt :=
    (linearIndependent_iff_injective_fintypeLinearCombination.mp base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 4 → F13 => g i) hfun
  by_cases hsi : i ∈ s <;> by_cases hti : i ∈ t <;> simp_all [gs, gt]

theorem subspace_mem_iff (x : AdjoinRoot f13) : x ∈ subspace ↔ ∃ s : Finset (Fin 4), x = subsetSum s := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact support_sum g
  · rintro ⟨s, hs⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 4 => if i ∈ s then (1 : F13) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, support_sum]
    have hsupport : support (fun i : Fin 4 => if i ∈ s then (1 : F13) else 0) = s := by
      ext i
      simp [support]
    rw [hsupport]
    change subsetSum s = x
    exact hs.symm

def indicator (s : Finset (Fin 4)) : Fin 4 → F13 := fun i => if i ∈ s then 1 else 0
def supportEquiv : (Fin 4 → F13) ≃ Finset (Fin 4) where
  toFun := support
  invFun := indicator
  left_inv g := by
    funext i
    exact (support_coeff g i).symm
  right_inv s := by
    ext i
    simp [support, indicator]

theorem underlyingFinset_subspace : Carlet.underlyingFinset subspace = Finset.univ.image subsetSum := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hx' : x ∈ subspace := (Carlet.mem_underlyingFinset subspace x).mp hx
    rcases (subspace_mem_iff x).mp hx' with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (Carlet.mem_underlyingFinset subspace x).mpr ((subspace_mem_iff x).mpr ⟨s, hs.symm⟩)

theorem erase_underlyingFinset_subspace :
    (Carlet.underlyingFinset subspace).erase 0 = Finset.image subsetSum (Finset.univ.erase (∅ : Finset (Fin 4))) := by
  classical
  rw [underlyingFinset_subspace]
  rw [Finset.image_erase subsetSum_injective Finset.univ (∅ : Finset (Fin 4))]
  simp [subsetSum]

theorem subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 4)), (subsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact subsetSum_injective h

end N13K4
end
