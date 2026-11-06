import Carlet.N17SubsetNonzeroProbe
import Carlet.N17FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
def c17Support (g : Fin 5 → F17) : Finset (Fin 5) := Finset.univ.filter (fun i => g i = 1)
lemma c17Support_coeff (g : Fin 5 → F17) (i : Fin 5) : g i = if i ∈ c17Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ c17Support g
  · have hgi : g i = 1 := by simpa [c17Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [c17Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma c17Support_sum (g : Fin 5 → F17) :
    (∑ i : Fin 5, g i • c17Base i) = ∑ i ∈ c17Support g, c17Base i := by
  classical
  simp_rw [c17Support_coeff]
  have ht (i : Fin 5) : (if i ∈ c17Support g then (1 : F17) else 0) • c17Base i = if i ∈ c17Support g then c17Base i else 0 := by
    by_cases h : i ∈ c17Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem c17Support_sum_ne_zero (s : Finset (Fin 5)) (hs : s.Nonempty) : (∑ i ∈ s, c17Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using c17SubsetSum01_nonzero
  case «2» => simpa using c17SubsetSum02_nonzero
  case «3» => simpa using c17SubsetSum03_nonzero
  case «4» => simpa using c17SubsetSum04_nonzero
  case «5» => simpa using c17SubsetSum05_nonzero
  case «6» => simpa using c17SubsetSum06_nonzero
  case «7» => simpa using c17SubsetSum07_nonzero
  case «8» => simpa using c17SubsetSum08_nonzero
  case «9» => simpa using c17SubsetSum09_nonzero
  case «10» => simpa using c17SubsetSum10_nonzero
  case «11» => simpa using c17SubsetSum11_nonzero
  case «12» => simpa using c17SubsetSum12_nonzero
  case «13» => simpa using c17SubsetSum13_nonzero
  case «14» => simpa using c17SubsetSum14_nonzero
  case «15» => simpa using c17SubsetSum15_nonzero
  case «16» => simpa using c17SubsetSum16_nonzero
  case «17» => simpa using c17SubsetSum17_nonzero
  case «18» => simpa using c17SubsetSum18_nonzero
  case «19» => simpa using c17SubsetSum19_nonzero
  case «20» => simpa using c17SubsetSum20_nonzero
  case «21» => simpa using c17SubsetSum21_nonzero
  case «22» => simpa using c17SubsetSum22_nonzero
  case «23» => simpa using c17SubsetSum23_nonzero
  case «24» => simpa using c17SubsetSum24_nonzero
  case «25» => simpa using c17SubsetSum25_nonzero
  case «26» => simpa using c17SubsetSum26_nonzero
  case «27» => simpa using c17SubsetSum27_nonzero
  case «28» => simpa using c17SubsetSum28_nonzero
  case «29» => simpa using c17SubsetSum29_nonzero
  case «30» => simpa using c17SubsetSum30_nonzero
  case «31» => simpa using c17SubsetSum31_nonzero
theorem c17Base_linearIndependent : LinearIndependent F17 c17Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (c17Support g).Nonempty := ⟨i, by simp [c17Support, hgi]⟩
  have hz : (∑ j ∈ c17Support g, c17Base j) = 0 := by
    calc
      _ = ∑ j : Fin 5, g j • c17Base j := (c17Support_sum g).symm
      _ = 0 := hg
  exact (c17Support_sum_ne_zero (c17Support g) hs) hz
#print axioms c17Base_linearIndependent


def c17Subspace : Submodule F17 (AdjoinRoot f17) := LinearMap.range (Fintype.linearCombination F17 c17Base)
theorem c17Subspace_finrank : Module.finrank F17 c17Subspace = 5 := by
  have hi : Function.Injective (Fintype.linearCombination F17 c17Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp c17Base_linearIndependent
  calc
    Module.finrank F17 c17Subspace = Module.finrank F17 (Fin 5 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 5 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms c17Subspace_finrank

theorem c17Subspace_mem_iff (x : AdjoinRoot f17) :
    x ∈ c17Subspace ↔ ∃ s : Finset (Fin 5), x = ∑ i ∈ s, c17Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨c17Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact c17Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 5 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, c17Support_sum]
    have hs : c17Support (fun i : Fin 5 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [c17Support]
    rw [hs]
#print axioms c17Subspace_mem_iff

def c17Indicator (s : Finset (Fin 5)) : Fin 5 → F17 := fun i => if i ∈ s then 1 else 0
def c17SupportEquiv : (Fin 5 → F17) ≃ Finset (Fin 5) where
  toFun := c17Support
  invFun := c17Indicator
  left_inv g := by
    funext i
    exact (c17Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [c17Support, c17Indicator]

def c17SubsetSum (s : Finset (Fin 5)) : AdjoinRoot f17 := ∑ i ∈ s, c17Base i
theorem c17SubsetSum_injective : Function.Injective c17SubsetSum := by
  intro s t h
  let gs := c17Indicator s
  let gt := c17Indicator t
  have hs : c17Support gs = s := c17SupportEquiv.right_inv s
  have ht : c17Support gt = t := c17SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 c17Base) gs = (Fintype.linearCombination F17 c17Base) gt := by
    rw [Fintype.linearCombination_apply, c17Support_sum, hs, Fintype.linearCombination_apply, c17Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp c17Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 5 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, c17Indicator]

theorem underlyingFinset_c17Subspace : Carlet.underlyingFinset c17Subspace = Finset.univ.image c17SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (c17Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (c17Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms c17SupportEquiv
#print axioms c17SubsetSum_injective
#print axioms underlyingFinset_c17Subspace

theorem c17SubsetSum_empty : c17SubsetSum (∅ : Finset (Fin 5)) = 0 := by simp [c17SubsetSum]
theorem erase_underlyingFinset_c17Subspace :
    (Carlet.underlyingFinset c17Subspace).erase 0 = Finset.image c17SubsetSum (Finset.univ.erase (∅ : Finset (Fin 5))) := by
  classical
  rw [underlyingFinset_c17Subspace]
  rw [Finset.image_erase c17SubsetSum_injective Finset.univ (∅ : Finset (Fin 5))]
  simp [c17SubsetSum]
theorem c17Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset c17Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 5)), (c17SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_c17Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact c17SubsetSum_injective h
#print axioms erase_underlyingFinset_c17Subspace
#print axioms c17Subspace_inverse_sum_eq_subset_sum


