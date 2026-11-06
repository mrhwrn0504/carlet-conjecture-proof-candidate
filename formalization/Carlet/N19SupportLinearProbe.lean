import Carlet.N19SubsetNonzeroProbe
import Carlet.N19FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
def c19Support (g : Fin 5 → F17) : Finset (Fin 5) := Finset.univ.filter (fun i => g i = 1)
lemma c19Support_coeff (g : Fin 5 → F17) (i : Fin 5) : g i = if i ∈ c19Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ c19Support g
  · have hgi : g i = 1 := by simpa [c19Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [c19Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma c19Support_sum (g : Fin 5 → F17) :
    (∑ i : Fin 5, g i • c19Base i) = ∑ i ∈ c19Support g, c19Base i := by
  classical
  simp_rw [c19Support_coeff]
  have ht (i : Fin 5) : (if i ∈ c19Support g then (1 : F17) else 0) • c19Base i = if i ∈ c19Support g then c19Base i else 0 := by
    by_cases h : i ∈ c19Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem c19Support_sum_ne_zero (s : Finset (Fin 5)) (hs : s.Nonempty) : (∑ i ∈ s, c19Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using c19SubsetSum01_nonzero
  case «2» => simpa using c19SubsetSum02_nonzero
  case «3» => simpa using c19SubsetSum03_nonzero
  case «4» => simpa using c19SubsetSum04_nonzero
  case «5» => simpa using c19SubsetSum05_nonzero
  case «6» => simpa using c19SubsetSum06_nonzero
  case «7» => simpa using c19SubsetSum07_nonzero
  case «8» => simpa using c19SubsetSum08_nonzero
  case «9» => simpa using c19SubsetSum09_nonzero
  case «10» => simpa using c19SubsetSum10_nonzero
  case «11» => simpa using c19SubsetSum11_nonzero
  case «12» => simpa using c19SubsetSum12_nonzero
  case «13» => simpa using c19SubsetSum13_nonzero
  case «14» => simpa using c19SubsetSum14_nonzero
  case «15» => simpa using c19SubsetSum15_nonzero
  case «16» => simpa using c19SubsetSum16_nonzero
  case «17» => simpa using c19SubsetSum17_nonzero
  case «18» => simpa using c19SubsetSum18_nonzero
  case «19» => simpa using c19SubsetSum19_nonzero
  case «20» => simpa using c19SubsetSum20_nonzero
  case «21» => simpa using c19SubsetSum21_nonzero
  case «22» => simpa using c19SubsetSum22_nonzero
  case «23» => simpa using c19SubsetSum23_nonzero
  case «24» => simpa using c19SubsetSum24_nonzero
  case «25» => simpa using c19SubsetSum25_nonzero
  case «26» => simpa using c19SubsetSum26_nonzero
  case «27» => simpa using c19SubsetSum27_nonzero
  case «28» => simpa using c19SubsetSum28_nonzero
  case «29» => simpa using c19SubsetSum29_nonzero
  case «30» => simpa using c19SubsetSum30_nonzero
  case «31» => simpa using c19SubsetSum31_nonzero
theorem c19Base_linearIndependent : LinearIndependent F17 c19Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (c19Support g).Nonempty := ⟨i, by simp [c19Support, hgi]⟩
  have hz : (∑ j ∈ c19Support g, c19Base j) = 0 := by
    calc
      _ = ∑ j : Fin 5, g j • c19Base j := (c19Support_sum g).symm
      _ = 0 := hg
  exact (c19Support_sum_ne_zero (c19Support g) hs) hz
#print axioms c19Base_linearIndependent


def c19Subspace : Submodule F17 (AdjoinRoot f19) := LinearMap.range (Fintype.linearCombination F17 c19Base)
theorem c19Subspace_finrank : Module.finrank F17 c19Subspace = 5 := by
  have hi : Function.Injective (Fintype.linearCombination F17 c19Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp c19Base_linearIndependent
  calc
    Module.finrank F17 c19Subspace = Module.finrank F17 (Fin 5 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 5 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms c19Subspace_finrank

theorem c19Subspace_mem_iff (x : AdjoinRoot f19) :
    x ∈ c19Subspace ↔ ∃ s : Finset (Fin 5), x = ∑ i ∈ s, c19Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨c19Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact c19Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 5 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, c19Support_sum]
    have hs : c19Support (fun i : Fin 5 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [c19Support]
    rw [hs]
#print axioms c19Subspace_mem_iff

def c19Indicator (s : Finset (Fin 5)) : Fin 5 → F17 := fun i => if i ∈ s then 1 else 0
def c19SupportEquiv : (Fin 5 → F17) ≃ Finset (Fin 5) where
  toFun := c19Support
  invFun := c19Indicator
  left_inv g := by
    funext i
    exact (c19Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [c19Support, c19Indicator]

def c19SubsetSum (s : Finset (Fin 5)) : AdjoinRoot f19 := ∑ i ∈ s, c19Base i
theorem c19SubsetSum_injective : Function.Injective c19SubsetSum := by
  intro s t h
  let gs := c19Indicator s
  let gt := c19Indicator t
  have hs : c19Support gs = s := c19SupportEquiv.right_inv s
  have ht : c19Support gt = t := c19SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 c19Base) gs = (Fintype.linearCombination F17 c19Base) gt := by
    rw [Fintype.linearCombination_apply, c19Support_sum, hs, Fintype.linearCombination_apply, c19Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp c19Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 5 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, c19Indicator]

theorem underlyingFinset_c19Subspace : Carlet.underlyingFinset c19Subspace = Finset.univ.image c19SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (c19Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (c19Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms c19SupportEquiv
#print axioms c19SubsetSum_injective
#print axioms underlyingFinset_c19Subspace

theorem c19SubsetSum_empty : c19SubsetSum (∅ : Finset (Fin 5)) = 0 := by simp [c19SubsetSum]
theorem erase_underlyingFinset_c19Subspace :
    (Carlet.underlyingFinset c19Subspace).erase 0 = Finset.image c19SubsetSum (Finset.univ.erase (∅ : Finset (Fin 5))) := by
  classical
  rw [underlyingFinset_c19Subspace]
  rw [Finset.image_erase c19SubsetSum_injective Finset.univ (∅ : Finset (Fin 5))]
  simp [c19SubsetSum]
theorem c19Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset c19Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 5)), (c19SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_c19Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact c19SubsetSum_injective h
#print axioms erase_underlyingFinset_c19Subspace
#print axioms c19Subspace_inverse_sum_eq_subset_sum


