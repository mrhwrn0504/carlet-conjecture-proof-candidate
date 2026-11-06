import Carlet.N9SubsetNonzeroProbe
import Carlet.N9FieldBridgeProbe
import Carlet.Statement
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial Carlet
set_option linter.unnecessarySimpa false
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
def d9Support (g : Fin 4 → F17) : Finset (Fin 4) := Finset.univ.filter (fun i => g i = 1)
lemma d9Support_coeff (g : Fin 4 → F17) (i : Fin 4) : g i = if i ∈ d9Support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ d9Support g
  · have hgi : g i = 1 := by simpa [d9Support] using hi
    rw [if_pos hi]; exact hgi
  · have hne : g i ≠ 1 := by simpa [d9Support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2; simpa [h0]
      · have hone : g i = 1 := by apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma d9Support_sum (g : Fin 4 → F17) :
    (∑ i : Fin 4, g i • d9Base i) = ∑ i ∈ d9Support g, d9Base i := by
  classical
  simp_rw [d9Support_coeff]
  have ht (i : Fin 4) : (if i ∈ d9Support g then (1 : F17) else 0) • d9Base i = if i ∈ d9Support g then d9Base i else 0 := by
    by_cases h : i ∈ d9Support g <;> simp [h]
  simp_rw [ht]
  simp
theorem d9Support_sum_ne_zero (s : Finset (Fin 4)) (hs : s.Nonempty) : (∑ i ∈ s, d9Base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using d9SubsetSum01_nonzero
  case «2» => simpa using d9SubsetSum02_nonzero
  case «3» => simpa using d9SubsetSum03_nonzero
  case «4» => simpa using d9SubsetSum04_nonzero
  case «5» => simpa using d9SubsetSum05_nonzero
  case «6» => simpa using d9SubsetSum06_nonzero
  case «7» => simpa using d9SubsetSum07_nonzero
  case «8» => simpa using d9SubsetSum08_nonzero
  case «9» => simpa using d9SubsetSum09_nonzero
  case «10» => simpa using d9SubsetSum10_nonzero
  case «11» => simpa using d9SubsetSum11_nonzero
  case «12» => simpa using d9SubsetSum12_nonzero
  case «13» => simpa using d9SubsetSum13_nonzero
  case «14» => simpa using d9SubsetSum14_nonzero
  case «15» => simpa using d9SubsetSum15_nonzero
theorem d9Base_linearIndependent : LinearIndependent F17 d9Base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by have hx := ZMod.val_lt (g i); omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by apply ZMod.val_injective 2; simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2; rw [h1]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
  have hs : (d9Support g).Nonempty := ⟨i, by simp [d9Support, hgi]⟩
  have hz : (∑ j ∈ d9Support g, d9Base j) = 0 := by
    calc
      _ = ∑ j : Fin 4, g j • d9Base j := (d9Support_sum g).symm
      _ = 0 := hg
  exact (d9Support_sum_ne_zero (d9Support g) hs) hz
#print axioms d9Base_linearIndependent


def d9Subspace : Submodule F17 (AdjoinRoot f9) := LinearMap.range (Fintype.linearCombination F17 d9Base)
theorem d9Subspace_finrank : Module.finrank F17 d9Subspace = 4 := by
  have hi : Function.Injective (Fintype.linearCombination F17 d9Base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp d9Base_linearIndependent
  calc
    Module.finrank F17 d9Subspace = Module.finrank F17 (Fin 4 → F17) := LinearMap.finrank_range_of_inj hi
    _ = 4 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms d9Subspace_finrank

theorem d9Subspace_mem_iff (x : AdjoinRoot f9) :
    x ∈ d9Subspace ↔ ∃ s : Finset (Fin 4), x = ∑ i ∈ s, d9Base i := by
  classical
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨g, hg⟩
    refine ⟨d9Support g, ?_⟩
    rw [← hg, Fintype.linearCombination_apply]
    exact d9Support_sum g
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨(fun i : Fin 4 => if i ∈ s then (1 : F17) else 0), ?_⟩
    rw [Fintype.linearCombination_apply, d9Support_sum]
    have hs : d9Support (fun i : Fin 4 => if i ∈ s then (1 : F17) else 0) = s := by
      ext i
      simp [d9Support]
    rw [hs]
#print axioms d9Subspace_mem_iff

def d9Indicator (s : Finset (Fin 4)) : Fin 4 → F17 := fun i => if i ∈ s then 1 else 0
def d9SupportEquiv : (Fin 4 → F17) ≃ Finset (Fin 4) where
  toFun := d9Support
  invFun := d9Indicator
  left_inv g := by
    funext i
    exact (d9Support_coeff g i).symm
  right_inv s := by
    ext i
    simp [d9Support, d9Indicator]

def d9SubsetSum (s : Finset (Fin 4)) : AdjoinRoot f9 := ∑ i ∈ s, d9Base i
theorem d9SubsetSum_injective : Function.Injective d9SubsetSum := by
  intro s t h
  let gs := d9Indicator s
  let gt := d9Indicator t
  have hs : d9Support gs = s := d9SupportEquiv.right_inv s
  have ht : d9Support gt = t := d9SupportEquiv.right_inv t
  have hlin : (Fintype.linearCombination F17 d9Base) gs = (Fintype.linearCombination F17 d9Base) gt := by
    rw [Fintype.linearCombination_apply, d9Support_sum, hs, Fintype.linearCombination_apply, d9Support_sum, ht]
    exact h
  have hfun : gs = gt := (linearIndependent_iff_injective_fintypeLinearCombination.mp d9Base_linearIndependent) hlin
  apply Finset.ext
  intro i
  have hv := congrArg (fun g : Fin 4 → F17 => g i) hfun
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [gs, gt, d9Indicator]

theorem underlyingFinset_d9Subspace : Carlet.underlyingFinset d9Subspace = Finset.univ.image d9SubsetSum := by
  classical
  ext x
  simp only [Carlet.mem_underlyingFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases (d9Subspace_mem_iff x).mp hx with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact (d9Subspace_mem_iff x).mpr ⟨s, hs.symm⟩
#print axioms d9SupportEquiv
#print axioms d9SubsetSum_injective
#print axioms underlyingFinset_d9Subspace

theorem d9SubsetSum_empty : d9SubsetSum (∅ : Finset (Fin 4)) = 0 := by simp [d9SubsetSum]
theorem erase_underlyingFinset_d9Subspace :
    (Carlet.underlyingFinset d9Subspace).erase 0 = Finset.image d9SubsetSum (Finset.univ.erase (∅ : Finset (Fin 4))) := by
  classical
  rw [underlyingFinset_d9Subspace]
  rw [Finset.image_erase d9SubsetSum_injective Finset.univ (∅ : Finset (Fin 4))]
  simp [d9SubsetSum]
theorem d9Subspace_inverse_sum_eq_subset_sum :
    (∑ x ∈ (Carlet.underlyingFinset d9Subspace).erase 0, x⁻¹) =
      ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin 4)), (d9SubsetSum s)⁻¹ := by
  classical
  rw [erase_underlyingFinset_d9Subspace]
  apply Finset.sum_image
  intro s hs t ht h
  exact d9SubsetSum_injective h
#print axioms erase_underlyingFinset_d9Subspace
#print axioms d9Subspace_inverse_sum_eq_subset_sum


