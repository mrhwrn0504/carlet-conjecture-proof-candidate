import Carlet.N11K5CompleteProbe
import Carlet.FieldTransport
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

namespace Carlet

theorem hasZeroSumSubspace_of_algHom_probe {K L : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [Field L] [Fintype L] [Algebra (ZMod 2) L]
    (e : K →ₐ[ZMod 2] L) (he : Function.Injective e) (k : ℕ)
    (h : HasZeroSumSubspace K k) : HasZeroSumSubspace L k := by
  classical
  obtain ⟨E, hdim, hz⟩ := h
  let E' := E.map e.toLinearMap
  let g : E →ₗ[ZMod 2] E' :=
    (e.toLinearMap.comp E.subtype).codRestrict E' (by
      intro x
      exact Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩)
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact he (congrArg Subtype.val hxy)
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let e' : E ≃ₗ[ZMod 2] E' := LinearEquiv.ofBijective g ⟨hg, hgsurj⟩
  have hdim' : Module.finrank (ZMod 2) E' = k := by
    calc
      Module.finrank (ZMod 2) E' = Module.finrank (ZMod 2) E := e'.finrank_eq.symm
      _ = k := hdim
  refine ⟨E', hdim', (zeroSum_full_iff E').mpr ?_⟩
  have himage : underlyingFinset E' = (underlyingFinset E).image e := by
    ext y
    simp only [mem_underlyingFinset, E', Submodule.mem_map, Finset.mem_image]
    constructor <;> rintro ⟨x, hx, hy⟩ <;> exact ⟨x, hx, hy⟩
  rw [himage, Finset.sum_image (by intro a ha b hb hab; exact he hab)]
  simp only [← map_inv₀ e, ← map_sum e]
  rw [(zeroSum_full_iff E).mp hz, map_zero]

theorem hasZeroSumSubspace_five_of_11_dvd_probe {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hdiv : 11 ∣ n) : HasZeroSumSubspace K 5 := by
  classical
  let L := AdjoinRoot f
  have hr : Module.finrank (ZMod 2) L = 11 := by
    have hcard : Fintype.card L = 2 ^ 11 := by simpa [L] using adjoinRoot11_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hcard
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hcard
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, hn] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 5 hasZeroSumSubspace_2048_probe

end Carlet

#print axioms Carlet.hasZeroSumSubspace_of_algHom_probe
#print axioms Carlet.hasZeroSumSubspace_five_of_11_dvd_probe


