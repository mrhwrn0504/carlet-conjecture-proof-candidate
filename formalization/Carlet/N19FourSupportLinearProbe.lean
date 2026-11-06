import Carlet.N19FourSubsetNonzeroProbe
import Carlet.N19FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
def e19Support (g : Fin 4 → F17) : Finset (Fin 4) := Finset.univ.filter (fun i => g i = 1)
lemma e19Support_coeff (g : Fin 4 → F17) (i : Fin 4) : g i = if i ∈ e19Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ e19Support g
  · have hgi : g i = 1 := by simpa [e19Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [e19Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma e19Support_sum (g : Fin 4 → F17) :
    (∑ i : Fin 4, g i • e19Base i) = ∑ i ∈ e19Support g, e19Base i := by
  classical
  simp_rw [e19Support_coeff]
  have ht (i : Fin 4) : (if i ∈ e19Support g then (1 : F17) else 0) • e19Base i = if i ∈ e19Support g then e19Base i else 0 := by
    by_cases h : i ∈ e19Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem e19Support_sum_ne_zero (s : Finset (Fin 4)) (hs : s.Nonempty) : (∑ i ∈ s, e19Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using e19SubsetSum01_nonzero
  case «2» => simpa using e19SubsetSum02_nonzero
  case «3» => simpa using e19SubsetSum03_nonzero
  case «4» => simpa using e19SubsetSum04_nonzero
  case «5» => simpa using e19SubsetSum05_nonzero
  case «6» => simpa using e19SubsetSum06_nonzero
  case «7» => simpa using e19SubsetSum07_nonzero
  case «8» => simpa using e19SubsetSum08_nonzero
  case «9» => simpa using e19SubsetSum09_nonzero
  case «10» => simpa using e19SubsetSum10_nonzero
  case «11» => simpa using e19SubsetSum11_nonzero
  case «12» => simpa using e19SubsetSum12_nonzero
  case «13» => simpa using e19SubsetSum13_nonzero
  case «14» => simpa using e19SubsetSum14_nonzero
  case «15» => simpa using e19SubsetSum15_nonzero
theorem e19Base_linearIndependent : LinearIndependent F17 e19Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (e19Support g).Nonempty := ⟨i, by simp [e19Support, hgi]⟩
  have hz : (∑ j ∈ e19Support g, e19Base j) = 0 := by
    calc
      _ = ∑ j : Fin 4, g j • e19Base j := (e19Support_sum g).symm
      _ = 0 := hg
  exact (e19Support_sum_ne_zero (e19Support g) hs) hz
#print axioms e19Base_linearIndependent


def e19Subspace : Submodule F17 (AdjoinRoot f19) := LinearMap.range (Fintype.linearCombination F17 e19Base)
theorem e19Subspace_finrank : Module.finrank F17 e19Subspace = 4 := by
  have hi : Function.Injective (Fintype.linearCombination F17 e19Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp e19Base_linearIndependent
  calc
    Module.finrank F17 e19Subspace = Module.finrank F17 (Fin 4 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 4 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms e19Subspace_finrank

theorem e19Subspace_mem_iff (x : AdjoinRoot f19) :
    x ∈ e19Subspace ↔ ∃ s : Finset (Fin 4), x = ∑ i ∈ s, e19Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨e19Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact e19Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 4 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, e19Support_sum]
    have hs : e19Support (fun i : Fin 4 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [e19Support]
    rw [hs]
#print axioms e19Subspace_mem_iff

def e19Indicator (s : Finset (Fin 4)) : Fin 4 → F17 := fun i => if i ∈ s then 1 else 0
def e19SupportEquiv : (Fin 4 → F17) ≃ Finset (Fin 4) where
  toFun := e19Support
  invFun := e19Indicator
  left_inv g := by
    funext i
    exact (e19Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [e19Support, e19Indicator]

def e19SubsetSum (s : Finset (Fin 4)) : AdjoinRoot f19 := ∑ i ∈ s, e19Base i
theorem e19SubsetSum_injective : Function.Injective e19SubsetSum := by
  intro s t h
  let gs := e19Indicator s
  let gt := e19Indicator t
  have hs : e19Support gs = s := e19SupportEquiv.right_inv s
  have ht : e19Support gt = t := e19SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 e19Base) gs = (Fintype.linearCombination F17 e19Base) gt := by
    rw [Fintype.linearCombination_apply, e19Support_sum, hs, Fintype.linearCombination_apply, e19Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp e19Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 4 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, e19Indicator]

theorem underlyingFinset_e19Subspace : Carlet.underlyingFinset e19Subspace = Finset.univ.image e19SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (e19Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (e19Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms e19SupportEquiv
#print axioms e19SubsetSum_injective
#print axioms underlyingFinset_e19Subspace

theorem e19SubsetSum_empty : e19SubsetSum (∅ : Finset (Fin 4)) = 0 := by simp [e19SubsetSum]
theorem erase_underlyingFinset_e19Subspace :
    (Carlet.underlyingFinset e19Subspace).erase 0 = Finset.image e19SubsetSum (Finset.univ.erase (∅ : Finset (Fin 4))) := by
  classical
  rw [underlyingFinset_e19Subspace]
  rw [Finset.image_erase e19SubsetSum_injective Finset.univ (∅ : Finset (Fin 4))]
  simp [e19SubsetSum]
theorem e19Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset e19Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 4)), (e19SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_e19Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact e19SubsetSum_injective h
#print axioms erase_underlyingFinset_e19Subspace
#print axioms e19Subspace_inverse_sum_eq_subset_sum


