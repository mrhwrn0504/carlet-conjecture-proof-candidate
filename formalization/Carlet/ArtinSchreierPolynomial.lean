import Carlet.ArtinSchreier

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem primeLine_polynomial :
    rootProduct (underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K))) = X^2+X := by
  have hs : underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K)) = {0,1} := by
    ext x
    simp only [mem_underlyingFinset, mem_span_singleton_two,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hs]
  simp [rootProduct, pow_two, mul_add]

theorem primeLine_eval (x : K) :
    (rootProduct (underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K)))).eval x =
      artinSchreier x := by
  rw [primeLine_polynomial, artinSchreier_apply]
  simp

theorem artinSchreier_subspace_polynomial (H : Submodule (ZMod 2) K) (hH : (1 : K) ∈ H) :
    (rootProduct (underlyingFinset (H.map artinSchreier))).comp (X^2+X) =
      rootProduct (underlyingFinset H) := by
  rw [← primeLine_polynomial (K := K)]
  apply monic_eq_rootProduct
  · exact (rootProduct_monic _).comp (rootProduct_monic _)
      (Nat.ne_of_gt (subspacePolynomial_natDegree_pos _))
  · rw [natDegree_comp, rootProduct_natDegree, rootProduct_natDegree,
      underlyingFinset_card_pow, underlyingFinset_card_pow, underlyingFinset_card_pow,
      finrank_span_singleton (one_ne_zero : (1 : K) ≠ 0), ← pow_add,
      artinSchreier_map_finrank H hH]
  · intro x hx
    rw [eval_comp, primeLine_eval]
    apply (subspacePolynomial_eval_eq_zero_iff (H.map artinSchreier) _).mpr
    exact ⟨x, (mem_underlyingFinset H x).mp hx, rfl⟩

#print axioms primeLine_polynomial
#print axioms artinSchreier_subspace_polynomial

end Carlet
