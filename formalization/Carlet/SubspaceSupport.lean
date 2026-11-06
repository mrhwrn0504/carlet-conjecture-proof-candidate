import Carlet.ArtinSchreierPolynomial
import Mathlib.Algebra.Polynomial.Expand

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def FrobeniusSupported (p : K[X]) : Prop :=
  ∀ i : ℕ, p.coeff i ≠ 0 → ∃ j : ℕ, i = 2^j

omit [Fintype K] [DecidableEq K] in
theorem coeff_square_charTwo (p : K[X]) (i : ℕ) :
    (p^2).coeff i = if 2 ∣ i then (p.coeff (i/2))^2 else 0 := by
  rw [← map_frobenius_expand 2 p, coeff_map, coeff_expand (by decide : 0 < 2)]
  split_ifs <;> simp [frobenius_def]

omit [Fintype K] [DecidableEq K] in
theorem frobeniusSupported_square {p : K[X]} (hp : FrobeniusSupported p) :
    FrobeniusSupported (p^2) := by
  intro i hi
  rw [coeff_square_charTwo] at hi
  split_ifs at hi with hd
  · have hc : p.coeff (i/2) ≠ 0 := by
      intro h
      simp [h] at hi
    obtain ⟨j,hj⟩ := hp (i/2) hc
    refine ⟨j+1, ?_⟩
    have hh := Nat.div_mul_cancel hd
    rw [hj] at hh
    rw [pow_succ]
    exact hh.symm
  · exact False.elim (hi rfl)

theorem subspacePolynomial_frobeniusSupported (E : Submodule (ZMod 2) K) :
    FrobeniusSupported (rootProduct (underlyingFinset E)) := by
  classical
  have hfg : E.FG := Submodule.FG.of_finite
  induction E, hfg using Submodule.fg_sup_span_induction with
  | bot =>
    have hbot : underlyingFinset (⊥ : Submodule (ZMod 2) K) = {0} := by
      ext x
      simp
    simp only [hbot, rootProduct, Finset.prod_singleton, C_0, add_zero]
    intro i hi
    have h : i = 1 := by
      by_contra h
      simp [coeff_X] at hi
      exact h hi.symm
    exact ⟨0, by simpa using h⟩
  | sup E v hfg ih =>
    by_cases hv : v ∈ E
    · have hs : E ⊔ Submodule.span (ZMod 2) ({v} : Set K) = E :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem v E).mpr hv)
      simpa [hs] using ih
    · rw [subspacePolynomial_extension E v hv]
      intro i hi
      rw [coeff_add, coeff_C_mul] at hi
      by_cases hs : (rootProduct (underlyingFinset E)^2).coeff i = 0
      · have hp : (rootProduct (underlyingFinset E)).coeff i ≠ 0 := by
          intro hp
          simp [hs,hp] at hi
        exact ih i hp
      · exact frobeniusSupported_square ih i hs

#print axioms coeff_square_charTwo
#print axioms subspacePolynomial_frobeniusSupported

end Carlet
