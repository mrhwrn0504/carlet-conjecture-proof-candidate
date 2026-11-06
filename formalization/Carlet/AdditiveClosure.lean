import Carlet.SubspaceScaling
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

/-- Linear constraints for a scalar to send F into I. -/
def scalingObstruction (F I : Submodule (ZMod 2) K) :
    K →ₗ[ZMod 2] (F →ₗ[ZMod 2] K ⧸ I) where
  toFun a := (I.mkQ.comp (LinearMap.mulLeft (ZMod 2) a)).comp F.subtype
  map_add' a b := by
    ext v
    change I.mkQ ((a + b) * (v : K)) = I.mkQ (a * (v : K)) + I.mkQ (b * (v : K))
    simp [add_mul]
  map_smul' c a := by
    ext v
    change I.mkQ ((c • a) * (v : K)) = c • I.mkQ (a * (v : K))
    rw [smul_mul_assoc, map_smul]

omit [DecidableEq K] in
theorem exists_scalarSubspace_le (F I : Submodule (ZMod 2) K)
    (h : Module.finrank (ZMod 2) F * Module.finrank (ZMod 2) (K ⧸ I) <
      Module.finrank (ZMod 2) K) :
    ∃ a : Kˣ, scalarSubspace F a ≤ I := by
  have hdim : Module.finrank (ZMod 2) (F →ₗ[ZMod 2] K ⧸ I) <
      Module.finrank (ZMod 2) K := by
    simpa only [Module.finrank_linearMap] using h
  have hker := LinearMap.ker_ne_bot_of_finrank_lt
    (f := scalingObstruction F I) hdim
  obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨Units.mk0 a hane, ?_⟩
  intro y hy
  obtain ⟨v, hv, hvy⟩ := hy
  have hz := congrArg (fun g : F →ₗ[ZMod 2] K ⧸ I => g ⟨v, hv⟩)
    (LinearMap.mem_ker.mp ha)
  change I.mkQ (a * v) = 0 at hz
  have hav : a * v ∈ I := by
    simpa using hz
  change a * v = y at hvy
  rwa [hvy] at hav

omit [DecidableEq K] in
theorem zeroSum_scalarSubspace (E : Submodule (ZMod 2) K) (a : Kˣ)
    (hE : IsZeroSum E) : IsZeroSum (scalarSubspace E a) := by
  rw [zeroSum_iff_coeff_two, ← scalarSubspace_subspacePolynomial E a, scaledPolynomial_coeff]
  rw [(zeroSum_iff_coeff_two E).mp hE, zero_mul, mul_zero]

def polynomialPreimage (E F : Submodule (ZMod 2) K) : Submodule (ZMod 2) K :=
  F.comap (subspacePolynomialMap E)

theorem polynomialPreimage_finrank (E F : Submodule (ZMod 2) K)
    (hF : F ≤ imageSubspace E) :
    Module.finrank (ZMod 2) (polynomialPreimage E F) =
      Module.finrank (ZMod 2) E + Module.finrank (ZMod 2) F := by
  let H := polynomialPreimage E F
  have hle : E ≤ H := by
    intro x hx
    change (rootProduct (underlyingFinset E)).eval x ∈ F
    rw [(subspacePolynomial_eval_eq_zero_iff E x).mpr hx]
    exact F.zero_mem
  have hk : Module.finrank (ZMod 2)
      (LinearMap.ker ((subspacePolynomialMap E).comp H.subtype)) =
      Module.finrank (ZMod 2) E := by
    rw [LinearMap.ker_comp, subspacePolynomialMap_ker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hd := LinearMap.finrank_range_add_finrank_ker
    ((subspacePolynomialMap E).comp H.subtype)
  rw [hk, LinearMap.range_comp, Submodule.range_subtype] at hd
  have hm : H.map (subspacePolynomialMap E) = F := Submodule.map_comap_eq_self hF
  rw [hm] at hd
  change Module.finrank (ZMod 2) H = _
  omega

theorem polynomialPreimage_polynomial (E F : Submodule (ZMod 2) K)
    (hF : F ≤ imageSubspace E) :
    (rootProduct (underlyingFinset F)).comp (rootProduct (underlyingFinset E)) =
      rootProduct (underlyingFinset (polynomialPreimage E F)) := by
  apply monic_eq_rootProduct
  · exact (rootProduct_monic _).comp (rootProduct_monic _)
      (Nat.ne_of_gt (subspacePolynomial_natDegree_pos E))
  · rw [natDegree_comp, rootProduct_natDegree, rootProduct_natDegree,
      underlyingFinset_card_pow, underlyingFinset_card_pow, underlyingFinset_card_pow,
      ← pow_add, polynomialPreimage_finrank E F hF, Nat.add_comm]
  · intro x hx
    rw [eval_comp]
    apply (subspacePolynomial_eval_eq_zero_iff F _).mpr
    exact (mem_underlyingFinset (polynomialPreimage E F) x).mp hx

theorem zeroSum_polynomialPreimage (E F : Submodule (ZMod 2) K)
    (hF : F ≤ imageSubspace E) (hEzero : IsZeroSum E) (hFzero : IsZeroSum F) :
    IsZeroSum (polynomialPreimage E F) := by
  rw [zeroSum_iff_coeff_two, ← polynomialPreimage_polynomial E F hF,
    coeff_comp_two _ _ (subspacePolynomial_coeff_zero E),
    (zeroSum_iff_coeff_two E).mp hEzero, (zeroSum_iff_coeff_two F).mp hFzero]
  simp

/-- Dimension addition for actual zero-sum subspaces; no external theorem is assumed. -/
theorem hasZeroSumSubspace_add (n k l : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hkl : k * l < n)
    (hk : HasZeroSumSubspace K k) (hl : HasZeroSumSubspace K l) :
    HasZeroSumSubspace K (k + l) := by
  obtain ⟨E, hE, hEzero⟩ := hk
  obtain ⟨F, hF, hFzero⟩ := hl
  have hquot : Module.finrank (ZMod 2) (K ⧸ imageSubspace E) = k := by
    have hq := (imageSubspace E).finrank_quotient_add_finrank
    have hi := image_finrank_add E
    rw [hE, hn] at hi
    rw [hn] at hq
    omega
  obtain ⟨a, ha⟩ := exists_scalarSubspace_le F (imageSubspace E) (by
    rw [hF, hquot, hn]
    simpa only [Nat.mul_comm] using hkl)
  refine ⟨polynomialPreimage E (scalarSubspace F a), ?_, ?_⟩
  · rw [polynomialPreimage_finrank E _ ha, scalarSubspace_finrank, hE, hF]
  · exact zeroSum_polynomialPreimage E _ ha hEzero (zeroSum_scalarSubspace F a hFzero)

#print axioms exists_scalarSubspace_le
#print axioms zeroSum_scalarSubspace
#print axioms polynomialPreimage_finrank
#print axioms polynomialPreimage_polynomial
#print axioms zeroSum_polynomialPreimage
#print axioms hasZeroSumSubspace_add

end Carlet
