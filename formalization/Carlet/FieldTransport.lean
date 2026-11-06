import Carlet.SubfieldFive
noncomputable section
open scoped BigOperators
namespace Carlet
variable {K L : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
  [Field L] [Fintype L] [Algebra (ZMod 2) L]

theorem zeroSum_full_iff (E : Submodule (ZMod 2) K) :
    IsZeroSum E ↔ (∑ x ∈ underlyingFinset E, x⁻¹) = 0 := by
  classical
  have hmem : (0 : K) ∈ underlyingFinset E := by simp
  have h := Finset.sum_erase_add (underlyingFinset E) (fun x : K => x⁻¹) hmem
  simp only [inv_zero, add_zero] at h
  exact h ▸ Iff.rfl

theorem hasZeroSumSubspace_of_algEquiv (e : K ≃ₐ[ZMod 2] L) (k : ℕ)
    (h : HasZeroSumSubspace K k) : HasZeroSumSubspace L k := by
  classical
  obtain ⟨E, hdim, hz⟩ := h
  let F := E.map e.toLinearEquiv.toLinearMap
  have hFdim : Module.finrank (ZMod 2) F = k := by
    rw [e.toLinearEquiv.finrank_map_eq, hdim]
  refine ⟨F, hFdim, (zeroSum_full_iff F).mpr ?_⟩
  have himage : underlyingFinset F = (underlyingFinset E).image e := by
    ext y
    simp only [mem_underlyingFinset, F, Submodule.mem_map, Finset.mem_image]
    constructor <;> rintro ⟨a, ha, hy⟩ <;> exact ⟨a, ha, hy⟩
  rw [himage, Finset.sum_image (by intro a ha b hb hab; exact e.injective hab)]
  simp only [← map_inv₀ e, ← map_sum e]
  rw [(zeroSum_full_iff E).mp hz, map_zero]

theorem hasZeroSumSubspace_of_card_eq (k : ℕ) (hcard : Fintype.card K = Fintype.card L)
    (h : HasZeroSumSubspace K k) : HasZeroSumSubspace L k := by
  exact hasZeroSumSubspace_of_algEquiv (FiniteField.algEquivOfCardEq 2 hcard) k h
#print axioms hasZeroSumSubspace_of_card_eq
#print axioms hasZeroSumSubspace_of_algEquiv
end Carlet
