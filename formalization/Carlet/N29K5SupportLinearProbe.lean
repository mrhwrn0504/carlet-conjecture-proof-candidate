import Carlet.N29K5SubsetNonzeroProbe
import Carlet.N29K5InvForTermProbe
import Carlet.N29K5FieldBridgeProbe
import Carlet.FieldTransport
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Carlet
set_option linter.unnecessarySeqFocus false
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
set_option maxHeartbeats 4000000
local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩
def n29K5Support (g : Fin 5 → F17) : Finset (Fin 5) := Finset.univ.filter (fun i => g i = 1)
lemma n29K5Support_coeff (g : Fin 5 → F17) (i : Fin 5) : g i = if i ∈ n29K5Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ n29K5Support g
  · have hgi : g i = 1 := by simpa [n29K5Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [n29K5Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma n29K5Support_sum (g : Fin 5 → F17) :
    (∑ i : Fin 5, g i • n29K5Base i) = ∑ i ∈ n29K5Support g, n29K5Base i := by
  classical
  simp_rw [n29K5Support_coeff]
  have ht (i : Fin 5) : (if i ∈ n29K5Support g then (1 : F17) else 0) • n29K5Base i = if i ∈ n29K5Support g then n29K5Base i else 0 := by
    by_cases h : i ∈ n29K5Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem n29K5Support_sum_ne_zero (s : Finset (Fin 5)) (hs : s.Nonempty) : (∑ i ∈ s, n29K5Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using n29K5SubsetSum01_nonzero
  case «2» => simpa using n29K5SubsetSum02_nonzero
  case «3» => simpa using n29K5SubsetSum03_nonzero
  case «4» => simpa using n29K5SubsetSum04_nonzero
  case «5» => simpa using n29K5SubsetSum05_nonzero
  case «6» => simpa using n29K5SubsetSum06_nonzero
  case «7» => simpa using n29K5SubsetSum07_nonzero
  case «8» => simpa using n29K5SubsetSum08_nonzero
  case «9» => simpa using n29K5SubsetSum09_nonzero
  case «10» => simpa using n29K5SubsetSum10_nonzero
  case «11» => simpa using n29K5SubsetSum11_nonzero
  case «12» => simpa using n29K5SubsetSum12_nonzero
  case «13» => simpa using n29K5SubsetSum13_nonzero
  case «14» => simpa using n29K5SubsetSum14_nonzero
  case «15» => simpa using n29K5SubsetSum15_nonzero
  case «16» => simpa using n29K5SubsetSum16_nonzero
  case «17» => simpa using n29K5SubsetSum17_nonzero
  case «18» => simpa using n29K5SubsetSum18_nonzero
  case «19» => simpa using n29K5SubsetSum19_nonzero
  case «20» => simpa using n29K5SubsetSum20_nonzero
  case «21» => simpa using n29K5SubsetSum21_nonzero
  case «22» => simpa using n29K5SubsetSum22_nonzero
  case «23» => simpa using n29K5SubsetSum23_nonzero
  case «24» => simpa using n29K5SubsetSum24_nonzero
  case «25» => simpa using n29K5SubsetSum25_nonzero
  case «26» => simpa using n29K5SubsetSum26_nonzero
  case «27» => simpa using n29K5SubsetSum27_nonzero
  case «28» => simpa using n29K5SubsetSum28_nonzero
  case «29» => simpa using n29K5SubsetSum29_nonzero
  case «30» => simpa using n29K5SubsetSum30_nonzero
  case «31» => simpa using n29K5SubsetSum31_nonzero
theorem n29K5Base_linearIndependent : LinearIndependent F17 n29K5Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (n29K5Support g).Nonempty := ⟨i, by simp [n29K5Support, hgi]⟩
  have hz : (∑ j ∈ n29K5Support g, n29K5Base j) = 0 := by
    calc
      _ = ∑ j : Fin 5, g j • n29K5Base j := (n29K5Support_sum g).symm
      _ = 0 := hg
  exact (n29K5Support_sum_ne_zero (n29K5Support g) hs) hz
#print axioms n29K5Base_linearIndependent


def n29K5Subspace : Submodule F17 (AdjoinRoot f29K5) := LinearMap.range (Fintype.linearCombination F17 n29K5Base)
theorem n29K5Subspace_finrank : Module.finrank F17 n29K5Subspace = 5 := by
  have hi : Function.Injective (Fintype.linearCombination F17 n29K5Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp n29K5Base_linearIndependent
  calc
    Module.finrank F17 n29K5Subspace = Module.finrank F17 (Fin 5 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 5 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms n29K5Subspace_finrank

theorem n29K5Subspace_mem_iff (x : AdjoinRoot f29K5) :
    x ∈ n29K5Subspace ↔ ∃ s : Finset (Fin 5), x = ∑ i ∈ s, n29K5Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨n29K5Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact n29K5Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 5 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, n29K5Support_sum]
    have hs : n29K5Support (fun i : Fin 5 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [n29K5Support]
    rw [hs]
#print axioms n29K5Subspace_mem_iff

def n29K5Indicator (s : Finset (Fin 5)) : Fin 5 → F17 := fun i => if i ∈ s then 1 else 0
def n29K5SupportEquiv : (Fin 5 → F17) ≃ Finset (Fin 5) where
  toFun := n29K5Support
  invFun := n29K5Indicator
  left_inv g := by
    funext i
    exact (n29K5Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [n29K5Support, n29K5Indicator]

theorem n29K5SubsetSum_injective : Function.Injective n29K5SubsetSum := by
  intro s t h
  let gs := n29K5Indicator s
  let gt := n29K5Indicator t
  have hs : n29K5Support gs = s := n29K5SupportEquiv.right_inv s
  have ht : n29K5Support gt = t := n29K5SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 n29K5Base) gs = (Fintype.linearCombination F17 n29K5Base) gt := by
    rw [Fintype.linearCombination_apply, n29K5Support_sum, hs, Fintype.linearCombination_apply, n29K5Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp n29K5Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 5 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, n29K5Indicator]

theorem underlyingFinset_n29K5Subspace : Carlet.underlyingFinset n29K5Subspace = Finset.univ.image n29K5SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (n29K5Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (n29K5Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms n29K5SupportEquiv
#print axioms n29K5SubsetSum_injective
#print axioms underlyingFinset_n29K5Subspace

theorem erase_underlyingFinset_n29K5Subspace :
    (Carlet.underlyingFinset n29K5Subspace).erase 0 = Finset.image n29K5SubsetSum (Finset.univ.erase (∅ : Finset (Fin 5))) := by
  classical
  rw [underlyingFinset_n29K5Subspace]
  rw [Finset.image_erase n29K5SubsetSum_injective Finset.univ (∅ : Finset (Fin 5))]
  simp [n29K5SubsetSum]
theorem n29K5Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset n29K5Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 5)), (n29K5SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_n29K5Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact n29K5SubsetSum_injective h
#print axioms erase_underlyingFinset_n29K5Subspace
#print axioms n29K5Subspace_inverse_sum_eq_subset_sum


