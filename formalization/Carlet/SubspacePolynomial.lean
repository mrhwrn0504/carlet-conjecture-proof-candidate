import Carlet.Statement
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

noncomputable section

open scoped BigOperators
open Polynomial

namespace Carlet

variable {K : Type*} [Field K]

theorem rootProduct_union [DecidableEq K] (s t : Finset K) (h : Disjoint s t) :
    rootProduct (s ∪ t) = rootProduct s * rootProduct t := by
  exact Finset.prod_union h

theorem rootProduct_translate [DecidableEq K] (s : Finset K) (v : K) :
    rootProduct (s.image (fun u => u + v)) = (rootProduct s).comp (X + C v) := by
  simp only [rootProduct]
  rw [Finset.prod_image, Polynomial.prod_comp]
  · apply Finset.prod_congr rfl
    intro u hu
    simp only [add_comp, X_comp, C_comp, map_add]
    ring
  · intro a ha b hb h
    exact add_right_cancel h

/-- Polynomial translation, not merely additivity of the evaluated function. -/
def HasTranslationIdentity (L : K[X]) : Prop :=
  ∀ v : K, L.comp (X + C v) = L + C (L.eval v)

theorem translationIdentity_X : HasTranslationIdentity (X : K[X]) := by
  intro v
  simp

theorem translationIdentity_step [CharP K 2] (L : K[X]) (c : K)
    (h : HasTranslationIdentity L) : HasTranslationIdentity (L ^ 2 + C c * L) := by
  intro v
  simp only [add_comp, pow_comp, mul_comp, C_comp, h v, eval_add, eval_pow,
    eval_mul, eval_C, map_add, map_mul, map_pow]
  rw [add_pow_char _ _ 2]
  ring

variable [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance fieldCharTwo : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

omit [Fintype K] [DecidableEq K] in
theorem mem_span_singleton_two (v x : K) :
    x ∈ Submodule.span (ZMod 2) ({v} : Set K) ↔ x = 0 ∨ x = v := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    fin_cases a
    · change (0 : ZMod 2) • v = 0 ∨ (0 : ZMod 2) • v = v
      simp
    · change (1 : ZMod 2) • v = 0 ∨ (1 : ZMod 2) • v = v
      simp
  · rintro (rfl | rfl)
    · exact Submodule.zero_mem _
    · exact Submodule.mem_span_singleton_self _

theorem underlyingFinset_sup_singleton (E : Submodule (ZMod 2) K) (v : K) :
    underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)) =
      underlyingFinset E ∪ (underlyingFinset E).image (fun u => u + v) := by
  classical
  ext x
  simp only [mem_underlyingFinset, Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp h
    rcases (mem_span_singleton_two v z).mp hz with rfl | rfl
    · left
      simpa using hu
    · exact Or.inr ⟨u, hu, rfl⟩
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact Submodule.mem_sup_left h
    · exact (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)).add_mem
        (Submodule.mem_sup_left hu)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))

theorem disjoint_subspace_translate (E : Submodule (ZMod 2) K) (v : K) (hv : v ∉ E) :
    Disjoint (underlyingFinset E) ((underlyingFinset E).image (fun u => u + v)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hy
  have hxu : x + u = v := by
    rw [← hux, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  apply hv
  rw [← hxu]
  exact E.add_mem ((mem_underlyingFinset E x).mp hx) ((mem_underlyingFinset E u).mp hu)

theorem rootProduct_sup_step (E : Submodule (ZMod 2) K) (v : K) (hv : v ∉ E)
    (hE : HasTranslationIdentity (rootProduct (underlyingFinset E))) :
    rootProduct (underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K))) =
      rootProduct (underlyingFinset E) ^ 2 +
        C ((rootProduct (underlyingFinset E)).eval v) * rootProduct (underlyingFinset E) := by
  classical
  rw [underlyingFinset_sup_singleton, rootProduct_union _ _ (disjoint_subspace_translate E v hv),
    rootProduct_translate, hE v]
  ring

theorem subspacePolynomial_translation (E : Submodule (ZMod 2) K) :
    HasTranslationIdentity (rootProduct (underlyingFinset E)) := by
  classical
  have hfg : E.FG := Submodule.FG.of_finite
  induction E, hfg using Submodule.fg_sup_span_induction with
  | bot =>
    have hbot : underlyingFinset (⊥ : Submodule (ZMod 2) K) = {0} := by
      ext x
      simp
    simpa [hbot, rootProduct] using (translationIdentity_X (K := K))
  | sup E v hfg ih =>
    by_cases hv : v ∈ E
    · have hs : E ⊔ Submodule.span (ZMod 2) ({v} : Set K) = E :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem v E).mpr hv)
      simpa [hs] using ih
    · rw [rootProduct_sup_step E v hv ih]
      exact translationIdentity_step _ _ ih

/-- Manuscript Lemma 2.3 for the actual enlarged F₂-linear subspace. -/
theorem subspacePolynomial_extension (E : Submodule (ZMod 2) K) (v : K) (hv : v ∉ E) :
    rootProduct (underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K))) =
      rootProduct (underlyingFinset E) ^ 2 +
        C ((rootProduct (underlyingFinset E)).eval v) * rootProduct (underlyingFinset E) :=
  rootProduct_sup_step E v hv (subspacePolynomial_translation E)

theorem subspacePolynomial_coeff_zero (E : Submodule (ZMod 2) K) :
    (rootProduct (underlyingFinset E)).coeff 0 = 0 := by
  rw [rootProduct_eq_X_mul_nonzeroRootProduct _ (by simp)]
  simp

omit [DecidableEq K] in
theorem subspacePolynomial_eval_eq_zero_iff (E : Submodule (ZMod 2) K) (v : K) :
    (rootProduct (underlyingFinset E)).eval v = 0 ↔ v ∈ E := by
  classical
  simp [rootProduct, Polynomial.eval_prod, Finset.prod_eq_zero_iff, CharTwo.add_eq_zero]

/-- The manuscript's final-step solver now refers to the actual extended subspace. -/
theorem extension_zeroSum_iff (E : Submodule (ZMod 2) K) (v : K) (hv : v ∉ E)
    (h1 : (rootProduct (underlyingFinset E)).coeff 2 ≠ 0) :
    IsZeroSum (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)) ↔
      (rootProduct (underlyingFinset E)).eval v =
        (rootProduct (underlyingFinset E)).coeff 1 ^ 2 /
          (rootProduct (underlyingFinset E)).coeff 2 := by
  rw [zeroSum_iff_coeff_two, subspacePolynomial_extension E v hv]
  exact extension_coeff_two_eq_zero_iff_char_two _ _ (subspacePolynomial_coeff_zero E) h1

/-- Evaluation of the actual subspace polynomial is an F₂-linear map. -/
def subspacePolynomialMap (E : Submodule (ZMod 2) K) : K →ₗ[ZMod 2] K where
  toFun := fun x => (rootProduct (underlyingFinset E)).eval x
  map_add' := by
    intro x y
    simpa only [eval_comp, eval_add, eval_X, eval_C] using
      congrArg (Polynomial.eval x) (subspacePolynomial_translation E y)
  map_smul' := by
    intro a x
    fin_cases a
    · change (rootProduct (underlyingFinset E)).eval ((0 : ZMod 2) • x) =
        (0 : ZMod 2) • (rootProduct (underlyingFinset E)).eval x
      simpa only [zero_smul] using
        (subspacePolynomial_eval_eq_zero_iff E 0).mpr E.zero_mem
    · change (rootProduct (underlyingFinset E)).eval ((1 : ZMod 2) • x) =
        (1 : ZMod 2) • (rootProduct (underlyingFinset E)).eval x
      simp

theorem subspacePolynomialMap_ker (E : Submodule (ZMod 2) K) :
    LinearMap.ker (subspacePolynomialMap E) = E := by
  ext x
  exact subspacePolynomial_eval_eq_zero_iff E x

omit [DecidableEq K] in
theorem extension_finrank (E : Submodule (ZMod 2) K) (v : K) (hv : v ∉ E) :
    Module.finrank (ZMod 2) ↥(E ⊔ Submodule.span (ZMod 2) ({v} : Set K)) =
      Module.finrank (ZMod 2) E + 1 :=
  Submodule.finrank_sup_span_singleton hv

/-- A solution of the linear equation automatically lies outside E, since
the target is nonzero. This is an existence reduction, not a proof that
the target lies in the image for every E. -/
theorem solver_yields_zeroSum_subspace (E : Submodule (ZMod 2) K)
    (h1 : (rootProduct (underlyingFinset E)).coeff 2 ≠ 0)
    (himage : (rootProduct (underlyingFinset E)).coeff 1 ^ 2 /
        (rootProduct (underlyingFinset E)).coeff 2 ∈ LinearMap.range (subspacePolynomialMap E)) :
    HasZeroSumSubspace K (Module.finrank (ZMod 2) E + 1) := by
  obtain ⟨v, hv⟩ := himage
  have h0 : (rootProduct (underlyingFinset E)).coeff 1 ≠ 0 :=
    rootProduct_coeff_one_ne _ (by simp)
  have hne : v ∉ E := by
    intro hmem
    have hz := (subspacePolynomial_eval_eq_zero_iff E v).mpr hmem
    have hval : (rootProduct (underlyingFinset E)).eval v =
        (rootProduct (underlyingFinset E)).coeff 1 ^ 2 /
          (rootProduct (underlyingFinset E)).coeff 2 := hv
    rw [hz] at hval
    exact (div_ne_zero (pow_ne_zero _ h0) h1) hval.symm
  refine ⟨E ⊔ Submodule.span (ZMod 2) ({v} : Set K), extension_finrank E v hne, ?_⟩
  exact (extension_zeroSum_iff E v hne h1).mpr hv

#print axioms subspacePolynomial_translation
#print axioms subspacePolynomial_extension
#print axioms subspacePolynomial_eval_eq_zero_iff
#print axioms extension_zeroSum_iff
#print axioms subspacePolynomialMap_ker
#print axioms solver_yields_zeroSum_subspace

end Carlet
