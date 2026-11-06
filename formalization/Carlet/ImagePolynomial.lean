import Carlet.SubspacePolynomial
import Carlet.CompositionCoefficients
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots

noncomputable section

open scoped BigOperators
open Polynomial

namespace Carlet

variable {K : Type*} [Field K]

theorem rootProduct_monic (s : Finset K) : (rootProduct s).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun a ha => monic_X_add_C a)

theorem rootProduct_natDegree (s : Finset K) : (rootProduct s).natDegree = s.card := by
  rw [rootProduct, Polynomial.natDegree_prod_of_monic s _ (fun a ha => monic_X_add_C a)]
  simp

variable [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance imageFieldCharTwo : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

omit [DecidableEq K] in
theorem underlyingFinset_card (E : Submodule (ZMod 2) K) :
    (underlyingFinset E).card = Nat.card E := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype (fun x : K => x ∈ E)).symm

omit [DecidableEq K] in
theorem underlyingFinset_card_pow (E : Submodule (ZMod 2) K) :
    (underlyingFinset E).card = 2 ^ Module.finrank (ZMod 2) E := by
  rw [underlyingFinset_card, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

def imageSubspace (E : Submodule (ZMod 2) K) : Submodule (ZMod 2) K :=
  LinearMap.range (subspacePolynomialMap E)

theorem image_finrank_add (E : Submodule (ZMod 2) K) :
    Module.finrank (ZMod 2) (imageSubspace E) + Module.finrank (ZMod 2) E =
      Module.finrank (ZMod 2) K := by
  have h := LinearMap.finrank_range_add_finrank_ker (subspacePolynomialMap E)
  rw [subspacePolynomialMap_ker] at h
  exact h

theorem image_card_mul (E : Submodule (ZMod 2) K) :
    (underlyingFinset (imageSubspace E)).card * (underlyingFinset E).card = Fintype.card K := by
  rw [underlyingFinset_card_pow, underlyingFinset_card_pow, ← pow_add, image_finrank_add]
  symm
  simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := K))

omit [DecidableEq K] in
theorem subspacePolynomial_natDegree_pos (E : Submodule (ZMod 2) K) :
    0 < (rootProduct (underlyingFinset E)).natDegree := by
  rw [rootProduct_natDegree]
  exact Finset.card_pos.mpr ⟨0, by simp⟩

omit [Fintype K] [DecidableEq K] in
theorem monic_eq_rootProduct (p : K[X]) (s : Finset K) (hm : p.Monic)
    (hd : p.natDegree = s.card) (hz : ∀ x ∈ s, p.eval x = 0) :
    p = rootProduct s := by
  have hr := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hz hd.le hm.ne_zero
  have hc : p.roots.card = p.natDegree := by rw [hr]; exact hd.symm
  have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc
  rw [hr] at hp
  change (∏ x ∈ s, (X - C x)) = p at hp
  simpa only [CharTwo.sub_eq_add, rootProduct] using hp.symm

/-- The image polynomial composes with the original polynomial to give
the product over the entire ambient finite field. -/
theorem imagePolynomial_comp (E : Submodule (ZMod 2) K) :
    (rootProduct (underlyingFinset (imageSubspace E))).comp
      (rootProduct (underlyingFinset E)) = rootProduct (Finset.univ : Finset K) := by
  apply monic_eq_rootProduct
  · exact (rootProduct_monic _).comp (rootProduct_monic _)
      (Nat.ne_of_gt (subspacePolynomial_natDegree_pos E))
  · rw [Polynomial.natDegree_comp, rootProduct_natDegree, rootProduct_natDegree,
      image_card_mul, Finset.card_univ]
  · intro x hx
    rw [Polynomial.eval_comp]
    apply (subspacePolynomial_eval_eq_zero_iff (imageSubspace E) _).mpr
    exact ⟨x, rfl⟩

omit [DecidableEq K] in
theorem rootProduct_univ :
    rootProduct (Finset.univ : Finset K) = X ^ Fintype.card K - X := by
  symm
  apply monic_eq_rootProduct
  · apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (Fintype.one_lt_card (α := K))
  · simpa only [Finset.card_univ] using
      FiniteField.X_pow_card_sub_X_natDegree_eq K (Fintype.one_lt_card (α := K))
  · intro x hx
    simp [FiniteField.pow_card]

theorem imagePolynomial_comp_eq (E : Submodule (ZMod 2) K) :
    (rootProduct (underlyingFinset (imageSubspace E))).comp
      (rootProduct (underlyingFinset E)) = X ^ Fintype.card K - X := by
  rw [imagePolynomial_comp, rootProduct_univ]

/-- Zero-sum is preserved by the image construction. The ambient field
must have more than two elements; this excludes the genuine small-field
exception where X^(card K) has a nonzero X² coefficient. -/
theorem zeroSum_image_iff (E : Submodule (ZMod 2) K) (hcard : 2 < Fintype.card K) :
    IsZeroSum E ↔ IsZeroSum (imageSubspace E) := by
  rw [zeroSum_iff_coeff_two, zeroSum_iff_coeff_two]
  have he1 := rootProduct_coeff_one_ne (underlyingFinset E) (by simp)
  have hu1 := rootProduct_coeff_one_ne (underlyingFinset (imageSubspace E)) (by simp)
  have hc := congrArg (fun p : K[X] => p.coeff 2) (imagePolynomial_comp_eq E)
  rw [coeff_comp_two _ _ (subspacePolynomial_coeff_zero E)] at hc
  have hz : (X ^ Fintype.card K - X : K[X]).coeff 2 = 0 := by
    simp [coeff_X_pow, coeff_X, (Nat.ne_of_gt hcard).symm]
  rw [hz] at hc
  constructor
  · intro he
    rw [he, mul_zero, zero_add] at hc
    exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ he1)
  · intro hu
    rw [hu, zero_mul, add_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left hu1

theorem zeroSumSubspace_complement (n k : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hcard : 2 < Fintype.card K)
    (h : HasZeroSumSubspace K k) : HasZeroSumSubspace K (n - k) := by
  obtain ⟨E, hk, hz⟩ := h
  refine ⟨imageSubspace E, ?_, (zeroSum_image_iff E hcard).mp hz⟩
  have hd := image_finrank_add E
  rw [hk, hn] at hd
  omega

theorem zeroSumSubspace_complement_iff (n k : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hcard : 2 < Fintype.card K) (hk : k ≤ n) :
    HasZeroSumSubspace K k ↔ HasZeroSumSubspace K (n - k) := by
  constructor
  · exact zeroSumSubspace_complement n k hn hcard
  · intro h
    have h' := zeroSumSubspace_complement n (n-k) hn hcard h
    have he : n - (n-k) = k := by omega
    rwa [he] at h'

omit [DecidableEq K] in
theorem finrank_eq_of_card (n : ℕ) (hcard : Fintype.card K = 2 ^ n) :
    Module.finrank (ZMod 2) K = n := by
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [ZMod.card] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hc.symm.trans hcard)

/-- Complementary dimension in the manuscript's cardinality convention. -/
theorem zeroSumSubspace_complement_of_card (n k : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hn : 2 ≤ n) (hk : k ≤ n) :
    HasZeroSumSubspace K k ↔ HasZeroSumSubspace K (n - k) := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hsize : 2 < Fintype.card K := by rw [hcard]; omega
  exact zeroSumSubspace_complement_iff n k (finrank_eq_of_card n hcard) hsize hk

#print axioms image_finrank_add
#print axioms image_card_mul
#print axioms imagePolynomial_comp_eq
#print axioms zeroSum_image_iff
#print axioms zeroSumSubspace_complement_iff
#print axioms zeroSumSubspace_complement_of_card

end Carlet
