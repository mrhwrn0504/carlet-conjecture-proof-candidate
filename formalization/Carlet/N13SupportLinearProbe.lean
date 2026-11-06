import Carlet.N13SubsetNonzeroProbe
import Carlet.N13FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
def cert13Support (g : Fin 5 → F13) : Finset (Fin 5) := Finset.univ.filter (fun i => g i = 1)
lemma cert13Support_coeff (g : Fin 5 → F13) (i : Fin 5) : g i = if i ∈ cert13Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ cert13Support g
  · have hgi : g i = 1 := by simpa [cert13Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [cert13Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma cert13Support_sum (g : Fin 5 → F13) :
    (∑ i : Fin 5, g i • cert13Base i) = ∑ i ∈ cert13Support g, cert13Base i := by
  classical
  simp_rw [cert13Support_coeff]
  have ht (i : Fin 5) : (if i ∈ cert13Support g then (1 : F13) else 0) • cert13Base i = if i ∈ cert13Support g then cert13Base i else 0 := by
    by_cases h : i ∈ cert13Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem cert13Support_sum_ne_zero (s : Finset (Fin 5)) (hs : s.Nonempty) : (∑ i ∈ s, cert13Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using cert13SubsetSum01_nonzero
  case «2» => simpa using cert13SubsetSum02_nonzero
  case «3» => simpa using cert13SubsetSum03_nonzero
  case «4» => simpa using cert13SubsetSum04_nonzero
  case «5» => simpa using cert13SubsetSum05_nonzero
  case «6» => simpa using cert13SubsetSum06_nonzero
  case «7» => simpa using cert13SubsetSum07_nonzero
  case «8» => simpa using cert13SubsetSum08_nonzero
  case «9» => simpa using cert13SubsetSum09_nonzero
  case «10» => simpa using cert13SubsetSum10_nonzero
  case «11» => simpa using cert13SubsetSum11_nonzero
  case «12» => simpa using cert13SubsetSum12_nonzero
  case «13» => simpa using cert13SubsetSum13_nonzero
  case «14» => simpa using cert13SubsetSum14_nonzero
  case «15» => simpa using cert13SubsetSum15_nonzero
  case «16» => simpa using cert13SubsetSum16_nonzero
  case «17» => simpa using cert13SubsetSum17_nonzero
  case «18» => simpa using cert13SubsetSum18_nonzero
  case «19» => simpa using cert13SubsetSum19_nonzero
  case «20» => simpa using cert13SubsetSum20_nonzero
  case «21» => simpa using cert13SubsetSum21_nonzero
  case «22» => simpa using cert13SubsetSum22_nonzero
  case «23» => simpa using cert13SubsetSum23_nonzero
  case «24» => simpa using cert13SubsetSum24_nonzero
  case «25» => simpa using cert13SubsetSum25_nonzero
  case «26» => simpa using cert13SubsetSum26_nonzero
  case «27» => simpa using cert13SubsetSum27_nonzero
  case «28» => simpa using cert13SubsetSum28_nonzero
  case «29» => simpa using cert13SubsetSum29_nonzero
  case «30» => simpa using cert13SubsetSum30_nonzero
  case «31» => simpa using cert13SubsetSum31_nonzero
theorem cert13Base_linearIndependent : LinearIndependent F13 cert13Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (cert13Support g).Nonempty := ⟨i, by simp [cert13Support, hgi]⟩
  have hz : (∑ j ∈ cert13Support g, cert13Base j) = 0 := by
    calc
      _ = ∑ j : Fin 5, g j • cert13Base j := (cert13Support_sum g).symm
      _ = 0 := hg
  exact (cert13Support_sum_ne_zero (cert13Support g) hs) hz
#print axioms cert13Base_linearIndependent


def cert13Subspace : Submodule F13 (AdjoinRoot f13) := LinearMap.range (Fintype.linearCombination F13 cert13Base)
theorem cert13Subspace_finrank : Module.finrank F13 cert13Subspace = 5 := by
  have hi : Function.Injective (Fintype.linearCombination F13 cert13Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp cert13Base_linearIndependent
  calc
    Module.finrank F13 cert13Subspace = Module.finrank F13 (Fin 5 → F13) := LinearMap.finrank_range_of_inj hi
    _ = 5 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms cert13Subspace_finrank

theorem cert13Subspace_mem_iff (x : AdjoinRoot f13) :
    x ∈ cert13Subspace ↔ ∃ s : Finset (Fin 5), x = ∑ i ∈ s, cert13Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨cert13Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact cert13Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 5 => if i ∈ s then (1 : F13) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, cert13Support_sum]
    have hs : cert13Support (fun i : Fin 5 => if i ∈ s then (1 : F13) else 0) = s := by
      ext i
      simp [cert13Support]
    rw [hs]
#print axioms cert13Subspace_mem_iff

def cert13Indicator (s : Finset (Fin 5)) : Fin 5 → F13 := fun i => if i ∈ s then 1 else 0
def cert13SupportEquiv : (Fin 5 → F13) ≃ Finset (Fin 5) where
  toFun := cert13Support
  invFun := cert13Indicator
  left_inv g := by
    funext i
    exact (cert13Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [cert13Support, cert13Indicator]

def cert13SubsetSum (s : Finset (Fin 5)) : AdjoinRoot f13 := ∑ i ∈ s, cert13Base i
theorem cert13SubsetSum_injective : Function.Injective cert13SubsetSum := by
  intro s t h
  let gs := cert13Indicator s
  let gt := cert13Indicator t
  have hs : cert13Support gs = s := cert13SupportEquiv.right_inv s
  have ht : cert13Support gt = t := cert13SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F13 cert13Base) gs = (Fintype.linearCombination F13 cert13Base) gt := by
    rw [Fintype.linearCombination_apply, cert13Support_sum, hs, Fintype.linearCombination_apply, cert13Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp cert13Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 5 → F13 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, cert13Indicator]

theorem underlyingFinset_cert13Subspace : Carlet.underlyingFinset cert13Subspace = Finset.univ.image cert13SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (cert13Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (cert13Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms cert13SupportEquiv
#print axioms cert13SubsetSum_injective
#print axioms underlyingFinset_cert13Subspace

theorem cert13SubsetSum_empty : cert13SubsetSum (∅ : Finset (Fin 5)) = 0 := by simp [cert13SubsetSum]
theorem erase_underlyingFinset_cert13Subspace :
    (Carlet.underlyingFinset cert13Subspace).erase 0 = Finset.image cert13SubsetSum (Finset.univ.erase (∅ : Finset (Fin 5))) := by
  classical
  rw [underlyingFinset_cert13Subspace]
  rw [Finset.image_erase cert13SubsetSum_injective Finset.univ (∅ : Finset (Fin 5))]
  simp [cert13SubsetSum]
theorem cert13Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset cert13Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 5)), (cert13SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_cert13Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact cert13SubsetSum_injective h
#print axioms erase_underlyingFinset_cert13Subspace
#print axioms cert13Subspace_inverse_sum_eq_subset_sum


