import Carlet.ImagePolynomial
import Mathlib.Data.Fintype.EquivFin

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- Formal polynomial additivity, stronger than additivity on the finite set K. -/
theorem subspacePolynomial_comp_add (E : Submodule (ZMod 2) K) (p q : K[X]) :
    (rootProduct (underlyingFinset E)).comp (p+q) =
      (rootProduct (underlyingFinset E)).comp p + (rootProduct (underlyingFinset E)).comp q := by
  classical
  have hfg : E.FG := Submodule.FG.of_finite
  induction E, hfg using Submodule.fg_sup_span_induction with
  | bot =>
    have hbot : underlyingFinset (⊥ : Submodule (ZMod 2) K) = {0} := by
      ext x
      simp
    simp [hbot, rootProduct]
  | sup E v hfg ih =>
    by_cases hv : v ∈ E
    · have hs : E ⊔ Submodule.span (ZMod 2) ({v} : Set K) = E :=
        sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem v E).mpr hv)
      simpa [hs] using ih
    · rw [subspacePolynomial_extension E v hv]
      simp only [add_comp, pow_comp, mul_comp, C_comp, ih]
      have h2 : (2 : K[X]) = 0 := by
        simpa using (CharP.cast_eq_zero (K[X]) 2)
      rw [add_sq, h2]
      ring

theorem imageSubspace_injective : Function.Injective (imageSubspace (K := K)) := by
  intro E F hEF
  let p := rootProduct (underlyingFinset E)
  let q := rootProduct (underlyingFinset F)
  let u := rootProduct (underlyingFinset (imageSubspace E))
  have he : u.comp p = X ^ Fintype.card K - X := imagePolynomial_comp_eq E
  have hf : u.comp q = X ^ Fintype.card K - X := by
    simpa only [u, hEF, q] using imagePolynomial_comp_eq F
  have hz : u.comp (p+q) = 0 := by
    rw [subspacePolynomial_comp_add, he, hf, CharTwo.add_self_eq_zero]
  have hd : (p+q).natDegree = 0 := by
    have hh := congrArg Polynomial.natDegree hz
    rw [Polynomial.natDegree_comp, natDegree_zero] at hh
    exact (Nat.mul_eq_zero.mp hh).resolve_left
      (Nat.ne_of_gt (subspacePolynomial_natDegree_pos (imageSubspace E)))
  have hc : (p+q).coeff 0 = 0 := by
    simp only [coeff_add, p, q, subspacePolynomial_coeff_zero, add_zero]
  have hpq : p+q = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, hc, C_0]
  have hpeq : p = q := (CharTwo.add_eq_zero).mp hpq
  apply Submodule.ext
  intro x
  rw [← subspacePolynomial_eval_eq_zero_iff E x, ← subspacePolynomial_eval_eq_zero_iff F x]
  change p.eval x = 0 ↔ q.eval x = 0
  rw [hpeq]

theorem imageSubspace_bijective : Function.Bijective (imageSubspace (K := K)) := by
  let : Finite (Submodule (ZMod 2) K) :=
    Finite.of_injective (fun E : Submodule (ZMod 2) K => (E : Set K)) SetLike.coe_injective
  exact ⟨imageSubspace_injective, Finite.surjective_of_injective imageSubspace_injective⟩

def imageSubspaceEquiv : Submodule (ZMod 2) K ≃ Submodule (ZMod 2) K :=
  Equiv.ofBijective imageSubspace imageSubspace_bijective

theorem image_finrank_iff (n k : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (hk : k ≤ n) (E : Submodule (ZMod 2) K) :
    Module.finrank (ZMod 2) E = k ↔ Module.finrank (ZMod 2) (imageSubspace E) = n-k := by
  have h := image_finrank_add E
  rw [hn] at h
  omega

def imageDimensionEquiv (n k : ℕ) (hn : Module.finrank (ZMod 2) K = n) (hk : k ≤ n) :
    {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k} ≃
      {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = n-k} :=
  imageSubspaceEquiv.subtypeEquiv (image_finrank_iff n k hn hk)

def imageZeroSumEquiv (n k : ℕ) (hn : Module.finrank (ZMod 2) K = n) (hk : k ≤ n)
    (hcard : 2 < Fintype.card K) :
    {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧ IsZeroSum E} ≃
      {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = n-k ∧ IsZeroSum E} :=
  imageSubspaceEquiv.subtypeEquiv (fun E =>
    and_congr (image_finrank_iff n k hn hk E) (zeroSum_image_iff E hcard))

theorem zeroSum_count_complement (n k : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (hk : k ≤ n) (hcard : 2 < Fintype.card K) :
    Nat.card {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧ IsZeroSum E} =
      Nat.card {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = n-k ∧ IsZeroSum E} :=
  Nat.card_congr (imageZeroSumEquiv n k hn hk hcard)

#print axioms subspacePolynomial_comp_add
#print axioms imageSubspace_injective
#print axioms imageSubspace_bijective
#print axioms imageDimensionEquiv
#print axioms zeroSum_count_complement

end Carlet
