import Carlet.N17FourSubsetNonzeroProbe
import Carlet.N17FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
def e17Support (g : Fin 4 → F17) : Finset (Fin 4) := Finset.univ.filter (fun i => g i = 1)
lemma e17Support_coeff (g : Fin 4 → F17) (i : Fin 4) : g i = if i ∈ e17Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ e17Support g
  · have hgi : g i = 1 := by simpa [e17Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [e17Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma e17Support_sum (g : Fin 4 → F17) :
    (∑ i : Fin 4, g i • e17Base i) = ∑ i ∈ e17Support g, e17Base i := by
  classical
  simp_rw [e17Support_coeff]
  have ht (i : Fin 4) : (if i ∈ e17Support g then (1 : F17) else 0) • e17Base i = if i ∈ e17Support g then e17Base i else 0 := by
    by_cases h : i ∈ e17Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem e17Support_sum_ne_zero (s : Finset (Fin 4)) (hs : s.Nonempty) : (∑ i ∈ s, e17Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using e17SubsetSum01_nonzero
  case «2» => simpa using e17SubsetSum02_nonzero
  case «3» => simpa using e17SubsetSum03_nonzero
  case «4» => simpa using e17SubsetSum04_nonzero
  case «5» => simpa using e17SubsetSum05_nonzero
  case «6» => simpa using e17SubsetSum06_nonzero
  case «7» => simpa using e17SubsetSum07_nonzero
  case «8» => simpa using e17SubsetSum08_nonzero
  case «9» => simpa using e17SubsetSum09_nonzero
  case «10» => simpa using e17SubsetSum10_nonzero
  case «11» => simpa using e17SubsetSum11_nonzero
  case «12» => simpa using e17SubsetSum12_nonzero
  case «13» => simpa using e17SubsetSum13_nonzero
  case «14» => simpa using e17SubsetSum14_nonzero
  case «15» => simpa using e17SubsetSum15_nonzero
theorem e17Base_linearIndependent : LinearIndependent F17 e17Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (e17Support g).Nonempty := ⟨i, by simp [e17Support, hgi]⟩
  have hz : (∑ j ∈ e17Support g, e17Base j) = 0 := by
    calc
      _ = ∑ j : Fin 4, g j • e17Base j := (e17Support_sum g).symm
      _ = 0 := hg
  exact (e17Support_sum_ne_zero (e17Support g) hs) hz
#print axioms e17Base_linearIndependent


def e17Subspace : Submodule F17 (AdjoinRoot f17) := LinearMap.range (Fintype.linearCombination F17 e17Base)
theorem e17Subspace_finrank : Module.finrank F17 e17Subspace = 4 := by
  have hi : Function.Injective (Fintype.linearCombination F17 e17Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp e17Base_linearIndependent
  calc
    Module.finrank F17 e17Subspace = Module.finrank F17 (Fin 4 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 4 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms e17Subspace_finrank

theorem e17Subspace_mem_iff (x : AdjoinRoot f17) :
    x ∈ e17Subspace ↔ ∃ s : Finset (Fin 4), x = ∑ i ∈ s, e17Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨e17Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact e17Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 4 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, e17Support_sum]
    have hs : e17Support (fun i : Fin 4 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [e17Support]
    rw [hs]
#print axioms e17Subspace_mem_iff

def e17Indicator (s : Finset (Fin 4)) : Fin 4 → F17 := fun i => if i ∈ s then 1 else 0
def e17SupportEquiv : (Fin 4 → F17) ≃ Finset (Fin 4) where
  toFun := e17Support
  invFun := e17Indicator
  left_inv g := by
    funext i
    exact (e17Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [e17Support, e17Indicator]

def e17SubsetSum (s : Finset (Fin 4)) : AdjoinRoot f17 := ∑ i ∈ s, e17Base i
theorem e17SubsetSum_injective : Function.Injective e17SubsetSum := by
  intro s t h
  let gs := e17Indicator s
  let gt := e17Indicator t
  have hs : e17Support gs = s := e17SupportEquiv.right_inv s
  have ht : e17Support gt = t := e17SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 e17Base) gs = (Fintype.linearCombination F17 e17Base) gt := by
    rw [Fintype.linearCombination_apply, e17Support_sum, hs, Fintype.linearCombination_apply, e17Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp e17Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 4 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, e17Indicator]

theorem underlyingFinset_e17Subspace : Carlet.underlyingFinset e17Subspace = Finset.univ.image e17SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (e17Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (e17Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms e17SupportEquiv
#print axioms e17SubsetSum_injective
#print axioms underlyingFinset_e17Subspace

theorem e17SubsetSum_empty : e17SubsetSum (∅ : Finset (Fin 4)) = 0 := by simp [e17SubsetSum]
theorem erase_underlyingFinset_e17Subspace :
    (Carlet.underlyingFinset e17Subspace).erase 0 = Finset.image e17SubsetSum (Finset.univ.erase (∅ : Finset (Fin 4))) := by
  classical
  rw [underlyingFinset_e17Subspace]
  rw [Finset.image_erase e17SubsetSum_injective Finset.univ (∅ : Finset (Fin 4))]
  simp [e17SubsetSum]
theorem e17Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset e17Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 4)), (e17SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_e17Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact e17SubsetSum_injective h
#print axioms erase_underlyingFinset_e17Subspace
#print axioms e17Subspace_inverse_sum_eq_subset_sum


