import Carlet.N11FourSubsetNonzeroProbe
import Carlet.N11FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
def e11Support (g : Fin 4 → F17) : Finset (Fin 4) := Finset.univ.filter (fun i => g i = 1)
lemma e11Support_coeff (g : Fin 4 → F17) (i : Fin 4) : g i = if i ∈ e11Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ e11Support g
  · have hgi : g i = 1 := by simpa [e11Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [e11Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma e11Support_sum (g : Fin 4 → F17) :
    (∑ i : Fin 4, g i • e11Base i) = ∑ i ∈ e11Support g, e11Base i := by
  classical
  simp_rw [e11Support_coeff]
  have ht (i : Fin 4) : (if i ∈ e11Support g then (1 : F17) else 0) • e11Base i = if i ∈ e11Support g then e11Base i else 0 := by
    by_cases h : i ∈ e11Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem e11Support_sum_ne_zero (s : Finset (Fin 4)) (hs : s.Nonempty) : (∑ i ∈ s, e11Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using e11SubsetSum01_nonzero
  case «2» => simpa using e11SubsetSum02_nonzero
  case «3» => simpa using e11SubsetSum03_nonzero
  case «4» => simpa using e11SubsetSum04_nonzero
  case «5» => simpa using e11SubsetSum05_nonzero
  case «6» => simpa using e11SubsetSum06_nonzero
  case «7» => simpa using e11SubsetSum07_nonzero
  case «8» => simpa using e11SubsetSum08_nonzero
  case «9» => simpa using e11SubsetSum09_nonzero
  case «10» => simpa using e11SubsetSum10_nonzero
  case «11» => simpa using e11SubsetSum11_nonzero
  case «12» => simpa using e11SubsetSum12_nonzero
  case «13» => simpa using e11SubsetSum13_nonzero
  case «14» => simpa using e11SubsetSum14_nonzero
  case «15» => simpa using e11SubsetSum15_nonzero
theorem e11Base_linearIndependent : LinearIndependent F17 e11Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (e11Support g).Nonempty := ⟨i, by simp [e11Support, hgi]⟩
  have hz : (∑ j ∈ e11Support g, e11Base j) = 0 := by
    calc
      _ = ∑ j : Fin 4, g j • e11Base j := (e11Support_sum g).symm
      _ = 0 := hg
  exact (e11Support_sum_ne_zero (e11Support g) hs) hz
#print axioms e11Base_linearIndependent


def e11Subspace : Submodule F17 (AdjoinRoot f) := LinearMap.range (Fintype.linearCombination F17 e11Base)
theorem e11Subspace_finrank : Module.finrank F17 e11Subspace = 4 := by
  have hi : Function.Injective (Fintype.linearCombination F17 e11Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp e11Base_linearIndependent
  calc
    Module.finrank F17 e11Subspace = Module.finrank F17 (Fin 4 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 4 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms e11Subspace_finrank

theorem e11Subspace_mem_iff (x : AdjoinRoot f) :
    x ∈ e11Subspace ↔ ∃ s : Finset (Fin 4), x = ∑ i ∈ s, e11Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨e11Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact e11Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 4 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, e11Support_sum]
    have hs : e11Support (fun i : Fin 4 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [e11Support]
    rw [hs]
#print axioms e11Subspace_mem_iff

def e11Indicator (s : Finset (Fin 4)) : Fin 4 → F17 := fun i => if i ∈ s then 1 else 0
def e11SupportEquiv : (Fin 4 → F17) ≃ Finset (Fin 4) where
  toFun := e11Support
  invFun := e11Indicator
  left_inv g := by
    funext i
    exact (e11Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [e11Support, e11Indicator]

def e11SubsetSum (s : Finset (Fin 4)) : AdjoinRoot f := ∑ i ∈ s, e11Base i
theorem e11SubsetSum_injective : Function.Injective e11SubsetSum := by
  intro s t h
  let gs := e11Indicator s
  let gt := e11Indicator t
  have hs : e11Support gs = s := e11SupportEquiv.right_inv s
  have ht : e11Support gt = t := e11SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 e11Base) gs = (Fintype.linearCombination F17 e11Base) gt := by
    rw [Fintype.linearCombination_apply, e11Support_sum, hs, Fintype.linearCombination_apply, e11Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp e11Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 4 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, e11Indicator]

theorem underlyingFinset_e11Subspace : Carlet.underlyingFinset e11Subspace = Finset.univ.image e11SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (e11Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (e11Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms e11SupportEquiv
#print axioms e11SubsetSum_injective
#print axioms underlyingFinset_e11Subspace

theorem e11SubsetSum_empty : e11SubsetSum (∅ : Finset (Fin 4)) = 0 := by simp [e11SubsetSum]
theorem erase_underlyingFinset_e11Subspace :
    (Carlet.underlyingFinset e11Subspace).erase 0 = Finset.image e11SubsetSum (Finset.univ.erase (∅ : Finset (Fin 4))) := by
  classical
  rw [underlyingFinset_e11Subspace]
  rw [Finset.image_erase e11SubsetSum_injective Finset.univ (∅ : Finset (Fin 4))]
  simp [e11SubsetSum]
theorem e11Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset e11Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 4)), (e11SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_e11Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact e11SubsetSum_injective h
#print axioms erase_underlyingFinset_e11Subspace
#print axioms e11Subspace_inverse_sum_eq_subset_sum


