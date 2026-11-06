import Carlet.ProbabilityEnergy
import Mathlib.FieldTheory.Finite.GaloisField
noncomputable section
open scoped BigOperators
namespace Carlet
theorem sum_inverse_finite_field_zero {L : Type*} [Field L] [Fintype L]
    (a : L) (ha0 : a ≠ 0) (ha1 : a ≠ 1) : (∑ x : L, x⁻¹) = 0 := by
  classical
  have hs : (∑ x : L, x) = 0 := by
    have h := Equiv.sum_comp (Equiv.mulLeft₀ a ha0) (fun x : L => x)
    simp only [Equiv.mulLeft₀_apply] at h
    rw [← Finset.mul_sum] at h
    have hmul : (a - 1) * (∑ x : L, x) = 0 := by linear_combination h
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ha1)
  simpa using Equiv.sum_comp (Equiv.inv L) (fun x : L => x) |>.trans hs
theorem embedded_finite_field_zero {L K : Type*} [Field L] [Fintype L]
    [Algebra (ZMod 2) L] [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (f : L →ₐ[ZMod 2] K) (a : L) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    HasZeroSumSubspace K (Module.finrank (ZMod 2) L) := by
  classical
  let E := f.toLinearMap.range
  refine ⟨E, LinearMap.finrank_range_of_inj f.injective, ?_⟩
  have himage : underlyingFinset E = Finset.univ.image f := by
    ext x
    simp [E, LinearMap.mem_range]
  have hsum : (∑ x ∈ underlyingFinset E, x⁻¹) = 0 := by
    rw [himage, Finset.sum_image (by intro x hx y hy hxy; exact f.injective hxy)]
    simp only [← map_inv₀ f, ← map_sum f]
    rw [sum_inverse_finite_field_zero a ha0 ha1, map_zero]
  change (∑ x ∈ (underlyingFinset E).erase 0, x⁻¹) = 0
  have hmem : (0 : K) ∈ underlyingFinset E := by simp [E]
  have h := Finset.sum_erase_add (underlyingFinset E) (fun x : K => x⁻¹) hmem
  simpa using h.trans hsum

theorem hasZeroSumSubspace_five_of_dvd {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (hdiv : 5 ∣ n) : HasZeroSumSubspace K 5 := by
  classical
  let L := GaloisField 2 5
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 5 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 32 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
    norm_num
  have ha : ∃ a : L, a ≠ 0 ∧ a ≠ 1 := by
    by_contra h
    push Not at h
    have hs : (Finset.univ : Finset L) ⊆ {0, 1} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr (h x hx0)
    have hcard := Finset.card_le_card hs
    rw [Finset.card_univ, hc] at hcard
    have hsmall : ({0, 1} : Finset L).card ≤ 2 := by simp
    omega
  obtain ⟨a, ha0, ha1⟩ := ha
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by simpa [hr, hn]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
  simpa [hr] using embedded_finite_field_zero f a ha0 ha1

#print axioms hasZeroSumSubspace_five_of_dvd
#print axioms embedded_finite_field_zero
#print axioms sum_inverse_finite_field_zero
end Carlet



