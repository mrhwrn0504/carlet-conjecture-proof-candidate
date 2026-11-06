import Carlet.TraceDuality

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def artinSchreier : K →ₗ[ZMod 2] K :=
  (FiniteField.frobeniusAlgHom (ZMod 2) K).toLinearMap + LinearMap.id

omit [Fintype K] in
theorem artinSchreier_apply (x : K) : artinSchreier x = x^2+x := by
  simp [artinSchreier, FiniteField.frobeniusAlgHom, ZMod.card]

theorem trace_square (x : K) :
    Algebra.trace (ZMod 2) K (x^2) = Algebra.trace (ZMod 2) K x := by
  have h := Algebra.trace_eq_of_algEquiv
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) x
  simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using h

omit [Fintype K] in
theorem artinSchreier_ker :
    LinearMap.ker (artinSchreier (K := K)) = Submodule.span (ZMod 2) ({1} : Set K) := by
  classical
  apply Submodule.ext
  intro x
  rw [LinearMap.mem_ker, artinSchreier_apply, mem_span_singleton_two]
  constructor
  · intro h
    have hm : x*(x+1) = 0 := by simpa only [mul_add, mul_one, ← pow_two] using h
    rcases mul_eq_zero.mp hm with hx | hx
    · exact Or.inl hx
    · exact Or.inr (CharTwo.add_eq_zero.mp hx)
  · rintro (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero]

theorem artinSchreier_range_le_trace_ker :
    LinearMap.range (artinSchreier (K := K)) ≤ LinearMap.ker (Algebra.trace (ZMod 2) K) := by
  rintro y ⟨x,rfl⟩
  change Algebra.trace (ZMod 2) K (artinSchreier x) = 0
  rw [artinSchreier_apply, map_add, trace_square, CharTwo.add_self_eq_zero]

theorem artinSchreier_range :
    LinearMap.range (artinSchreier (K := K)) = LinearMap.ker (Algebra.trace (ZMod 2) K) := by
  apply Submodule.eq_of_le_of_finrank_le artinSchreier_range_le_trace_ker
  have ha := LinearMap.finrank_range_add_finrank_ker (artinSchreier (K := K))
  rw [artinSchreier_ker, finrank_span_singleton (one_ne_zero : (1 : K) ≠ 0)] at ha
  have ht := LinearMap.finrank_range_add_finrank_ker (Algebra.trace (ZMod 2) K)
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective (ZMod 2) K),
    finrank_top, Module.finrank_self] at ht
  omega

def artinSchreierSubspaceEquiv :
    {H : Submodule (ZMod 2) K // (1 : K) ∈ H} ≃
      {V : Submodule (ZMod 2) K // V ≤ LinearMap.ker (Algebra.trace (ZMod 2) K)} where
  toFun H := ⟨H.val.map artinSchreier,
    (LinearMap.map_le_range).trans artinSchreier_range_le_trace_ker⟩
  invFun V := ⟨V.val.comap artinSchreier, by
    change artinSchreier (1 : K) ∈ V.val
    simp [artinSchreier_apply, CharTwo.add_self_eq_zero]⟩
  left_inv H := by
    apply Subtype.ext
    apply Submodule.comap_map_eq_self
    rw [artinSchreier_ker]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr H.property
  right_inv V := by
    apply Subtype.ext
    apply Submodule.map_comap_eq_of_le
    rw [artinSchreier_range]
    exact V.property

theorem artinSchreier_map_finrank (H : Submodule (ZMod 2) K) (hH : (1 : K) ∈ H) :
    Module.finrank (ZMod 2) (H.map artinSchreier) + 1 = Module.finrank (ZMod 2) H := by
  have hle : Submodule.span (ZMod 2) ({1} : Set K) ≤ H :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hH
  have hk : Module.finrank (ZMod 2) (LinearMap.ker (artinSchreier.comp H.subtype)) = 1 := by
    rw [LinearMap.ker_comp, artinSchreier_ker]
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
      finrank_span_singleton (one_ne_zero : (1 : K) ≠ 0)]
  have h := LinearMap.finrank_range_add_finrank_ker (artinSchreier.comp H.subtype)
  rw [hk, LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

#print axioms trace_square
#print axioms artinSchreier_ker
#print axioms artinSchreier_range
#print axioms artinSchreierSubspaceEquiv
#print axioms artinSchreier_map_finrank

end Carlet
