import Carlet.N11SubsetNonzeroProbe
import Carlet.N11FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
def certSupport (g : Fin 5 → F) : Finset (Fin 5) := Finset.univ.filter (fun i => g i = 1)
lemma certSupport_coeff (g : Fin 5 → F) (i : Fin 5) : g i = if i ∈ certSupport g then 1 else 0 := by
  classical
  by_cases hi : i ∈ certSupport g
  · have hgi : g i = 1 := by simpa [certSupport] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [certSupport] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma certSupport_sum (g : Fin 5 → F) :
    (∑ i : Fin 5, g i • certBase i) = ∑ i ∈ certSupport g, certBase i := by
  classical
  simp_rw [certSupport_coeff]
  have ht (i : Fin 5) : (if i ∈ certSupport g then (1 : F) else 0) • certBase i = if i ∈ certSupport g then certBase i else 0 := by
    by_cases h : i ∈ certSupport g <;> simp [h]
  simp_rw [ht]
  simp
theorem certSupport_sum_ne_zero (s : Finset (Fin 5)) (hs : s.Nonempty) : (∑ i ∈ s, certBase i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using certSubsetSum01_nonzero
  case «2» => simpa using certSubsetSum02_nonzero
  case «3» => simpa using certSubsetSum03_nonzero
  case «4» => simpa using certSubsetSum04_nonzero
  case «5» => simpa using certSubsetSum05_nonzero
  case «6» => simpa using certSubsetSum06_nonzero
  case «7» => simpa using certSubsetSum07_nonzero
  case «8» => simpa using certSubsetSum08_nonzero
  case «9» => simpa using certSubsetSum09_nonzero
  case «10» => simpa using certSubsetSum10_nonzero
  case «11» => simpa using certSubsetSum11_nonzero
  case «12» => simpa using certSubsetSum12_nonzero
  case «13» => simpa using certSubsetSum13_nonzero
  case «14» => simpa using certSubsetSum14_nonzero
  case «15» => simpa using certSubsetSum15_nonzero
  case «16» => simpa using certSubsetSum16_nonzero
  case «17» => simpa using certSubsetSum17_nonzero
  case «18» => simpa using certSubsetSum18_nonzero
  case «19» => simpa using certSubsetSum19_nonzero
  case «20» => simpa using certSubsetSum20_nonzero
  case «21» => simpa using certSubsetSum21_nonzero
  case «22» => simpa using certSubsetSum22_nonzero
  case «23» => simpa using certSubsetSum23_nonzero
  case «24» => simpa using certSubsetSum24_nonzero
  case «25» => simpa using certSubsetSum25_nonzero
  case «26» => simpa using certSubsetSum26_nonzero
  case «27» => simpa using certSubsetSum27_nonzero
  case «28» => simpa using certSubsetSum28_nonzero
  case «29» => simpa using certSubsetSum29_nonzero
  case «30» => simpa using certSubsetSum30_nonzero
  case «31» => simpa using certSubsetSum31_nonzero
theorem certBase_linearIndependent : LinearIndependent F certBase := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (certSupport g).Nonempty := ⟨i, by simp [certSupport, hgi]⟩
  have hz : (∑ j ∈ certSupport g, certBase j) = 0 := by
    calc
      _ = ∑ j : Fin 5, g j • certBase j := (certSupport_sum g).symm
      _ = 0 := hg
  exact (certSupport_sum_ne_zero (certSupport g) hs) hz
#print axioms certBase_linearIndependent


def certSubspace : Submodule F (AdjoinRoot f) := LinearMap.range (Fintype.linearCombination F certBase)
theorem certSubspace_finrank : Module.finrank F certSubspace = 5 := by
  have hi : Function.Injective (Fintype.linearCombination F certBase) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp certBase_linearIndependent
  calc
    Module.finrank F certSubspace = Module.finrank F (Fin 5 → F) := LinearMap.finrank_range_of_inj hi
    _ = 5 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms certSubspace_finrank

theorem certSubspace_mem_iff (x : AdjoinRoot f) :
    x ∈ certSubspace ↔ ∃ s : Finset (Fin 5), x = ∑ i ∈ s, certBase i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨certSupport g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact certSupport_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 5 => if i ∈ s then (1 : F) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, certSupport_sum]
    have hs : certSupport (fun i : Fin 5 => if i ∈ s then (1 : F) else 0) = s := by
      ext i
      simp [certSupport]
    rw [hs]
#print axioms certSubspace_mem_iff

def certIndicator (s : Finset (Fin 5)) : Fin 5 → F := fun i => if i ∈ s then 1 else 0
def certSupportEquiv : (Fin 5 → F) ≃ Finset (Fin 5) where
  toFun := certSupport
  invFun := certIndicator
  left_inv g := by
    funext i
    exact (certSupport_coeff g i).symm
  right_inv s := by
    ext i
    simp [certSupport, certIndicator]

def certSubsetSum (s : Finset (Fin 5)) : AdjoinRoot f := ∑ i ∈ s, certBase i
theorem certSubsetSum_injective : Function.Injective certSubsetSum := by
  intro s t h
  let gs := certIndicator s
  let gt := certIndicator t
  have hs : certSupport gs = s := certSupportEquiv.right_inv s
  have ht : certSupport gt = t := certSupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F certBase) gs = (Fintype.linearCombination F certBase) gt := by
    rw [Fintype.linearCombination_apply, certSupport_sum, hs, Fintype.linearCombination_apply, certSupport_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp certBase_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 5 → F => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, certIndicator]

theorem underlyingFinset_certSubspace : Carlet.underlyingFinset certSubspace = Finset.univ.image certSubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (certSubspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (certSubspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms certSupportEquiv
#print axioms certSubsetSum_injective
#print axioms underlyingFinset_certSubspace

theorem certSubsetSum_empty : certSubsetSum (∅ : Finset (Fin 5)) = 0 := by simp [certSubsetSum]
theorem erase_underlyingFinset_certSubspace :
    (Carlet.underlyingFinset certSubspace).erase 0 = Finset.image certSubsetSum (Finset.univ.erase (∅ : Finset (Fin 5))) := by
  classical
  rw [underlyingFinset_certSubspace]
  rw [Finset.image_erase certSubsetSum_injective Finset.univ (∅ : Finset (Fin 5))]
  simp [certSubsetSum]
theorem certSubspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset certSubspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 5)), (certSubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_certSubspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact certSubsetSum_injective h
#print axioms erase_underlyingFinset_certSubspace
#print axioms certSubspace_inverse_sum_eq_subset_sum


