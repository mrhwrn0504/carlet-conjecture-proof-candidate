import Carlet.DualSubspacePolynomial

noncomputable section
namespace Carlet
open Polynomial

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
  [DecidableEq K]

local instance theta5FieldCharTwo : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

omit [Fintype K] [DecidableEq K] in
/-- Frobenius squaring shifts the coefficient at `2^j` to `2^(j+1)`.
    This is the coefficient-level recurrence needed to turn the subspace
    polynomial extension formula into a finite recurrence on its linearized
    coefficients. -/
theorem coeff_square_charTwo_pow (p : K[X]) (j : ℕ) :
    (p^2).coeff (2^(j+1)) = (p.coeff (2^j))^2 := by
  rw [coeff_square_charTwo]
  have hd : 2 ∣ 2^(j+1) := by
    refine ⟨2^j, ?_⟩
    rw [pow_succ]
    omega
  have hdiv : 2^(j+1) / 2 = 2^j := by
    rw [pow_succ]
    simp
  simp [hd, hdiv]

omit [Fintype K] [DecidableEq K] in
/-- One extension step updates each non-leading Frobenius coefficient by
    `a_j ↦ a_(j-1)^2 + L(v) a_j`. -/
theorem coeff_subspaceExtension_pow (p : K[X]) (c : K) (j : ℕ) :
    (p^2 + C c * p).coeff (2^(j+1)) =
      (p.coeff (2^j))^2 + c * p.coeff (2^(j+1)) := by
  rw [coeff_add, coeff_square_charTwo_pow]
  simp [coeff_C_mul]

/-- The actual finite-subspace polynomial inherits the coefficient recurrence
    when adjoining one independent vector. -/
theorem rootProduct_sup_step_coeff_pow (E : Submodule (ZMod 2) K)
    (v : K) (hv : v ∉ E) (j : ℕ) :
    (rootProduct (underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)))).coeff
        (2^(j+1)) =
      ((rootProduct (underlyingFinset E)).coeff (2^j))^2 +
        ((rootProduct (underlyingFinset E)).eval v) *
          (rootProduct (underlyingFinset E)).coeff (2^(j+1)) := by
  rw [subspacePolynomial_extension E v hv]
  exact coeff_subspaceExtension_pow _ _ _

/-- If the starting subspace polynomial is monic of degree 16, adjoining one
    vector makes its degree-16 coefficient vanish exactly when the extension
    point solves the rank-four linearized equation. -/
theorem rootProduct_sup_step_coeff16_zero_iff (E : Submodule (ZMod 2) K)
    (v : K) (hv : v ∉ E)
    (htop : (rootProduct (underlyingFinset E)).coeff 16 = 1) :
    (rootProduct (underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)))).coeff 16 = 0 ↔
      (rootProduct (underlyingFinset E)).eval v =
        ((rootProduct (underlyingFinset E)).coeff 8)^2 := by
  have hpow : 2^(3+1) = 16 := by norm_num
  have hrec := rootProduct_sup_step_coeff_pow E v hv 3
  rw [hpow] at hrec
  rw [hrec, htop]
  constructor
  · intro hz
    exact (CharTwo.add_eq_zero.mp (by simpa using hz)).symm
  · intro heval
    exact CharTwo.add_eq_zero.mpr (by simpa using heval.symm)

/-- The coefficient criterion for adjoining a point to any four-dimensional
    subspace, with the top coefficient discharged from its cardinality. -/
theorem rankFour_extend_zeroSumCoeff_iff (E : Submodule (ZMod 2) K)
    (hE : Module.finrank (ZMod 2) E = 4) (v : K) (hv : v ∉ E) :
    (rootProduct (underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)))).coeff 16 = 0 ↔
      (rootProduct (underlyingFinset E)).eval v =
        ((rootProduct (underlyingFinset E)).coeff 8)^2 := by
  apply rootProduct_sup_step_coeff16_zero_iff E v hv
  have hdeg : (rootProduct (underlyingFinset E)).natDegree = 16 := by
    rw [rootProduct_natDegree, underlyingFinset_card_pow, hE]
    norm_num
  rw [← hdeg]
  exact (rootProduct_monic _).coeff_natDegree

/-- For a rank-five subspace, the next-to-leading coefficient criterion for
    its dual-image subspace is exactly the vanishing of the X^16 coefficient.
    The explicit Θ₅ polynomial must still be identified with this coefficient
    after choosing a basis of the dual-image space. -/
theorem zeroSum_dualImage_iff_coeff16 (E : Submodule (ZMod 2) K)
    (hE : Module.finrank (ZMod 2) E = 5) :
    IsZeroSum (dualImageEquiv E) ↔
      (rootProduct (underlyingFinset E)).coeff 16 = 0 := by
  rw [zeroSum_dualImage_iff E (by rw [hE]; omega)]
  unfold nextFrobeniusCoefficient
  rw [hE]
  norm_num

/-- The original rank-five existence problem is exactly the problem of finding
    a five-dimensional subspace whose subspace-polynomial X^16 coefficient
    vanishes. This is the coefficient-level Θ₅ interface, with no weakened
    quantifiers. -/
theorem hasZeroSumSubspace_five_iff_exists_coeff16 :
    HasZeroSumSubspace K 5 ↔
      ∃ E : Submodule (ZMod 2) K,
        Module.finrank (ZMod 2) E = 5 ∧
          (rootProduct (underlyingFinset E)).coeff 16 = 0 := by
  constructor
  · rintro ⟨V, hV, hzero⟩
    let E := (dualImageEquiv (K := K)).symm V
    have hE : Module.finrank (ZMod 2) E = 5 := by
      calc
        Module.finrank (ZMod 2) E =
            Module.finrank (ZMod 2) (dualImageEquiv E) := by
          rw [dualImage_finrank]
        _ = Module.finrank (ZMod 2) V := by
          rw [show dualImageEquiv E = V from Equiv.apply_symm_apply _ _]
        _ = 5 := hV
    refine ⟨E, hE, ?_⟩
    have hiff := zeroSum_dualImage_iff_coeff16 E hE
    rw [show dualImageEquiv E = V from Equiv.apply_symm_apply _ _] at hiff
    exact hiff.mp hzero
  · rintro ⟨E, hE, hcoeff⟩
    refine ⟨dualImageEquiv E, ?_, ?_⟩
    · rw [dualImage_finrank, hE]
    · exact (zeroSum_dualImage_iff_coeff16 E hE).mpr hcoeff

/-- A four-dimensional subspace and an outside solution of its linearized
    equation produce a five-dimensional zero-sum subspace. -/
theorem rankFour_extension_solution_gives_k5 (E : Submodule (ZMod 2) K)
    (hE : Module.finrank (ZMod 2) E = 4) (v : K) (hv : v ∉ E)
    (heval : (rootProduct (underlyingFinset E)).eval v =
      ((rootProduct (underlyingFinset E)).coeff 8)^2) :
    HasZeroSumSubspace K 5 := by
  let W := E ⊔ Submodule.span (ZMod 2) ({v} : Set K)
  have hW : Module.finrank (ZMod 2) W = 5 := by
    dsimp [W]
    rw [extension_finrank E v hv, hE]
  have hcoeff : (rootProduct (underlyingFinset W)).coeff 16 = 0 :=
    (rankFour_extend_zeroSumCoeff_iff E hE v hv).mpr heval
  exact (hasZeroSumSubspace_five_iff_exists_coeff16 (K := K)).mpr
    ⟨W, hW, hcoeff⟩

/-- A nonzero target in the range of the rank-four subspace-polynomial map
    supplies the outside point required by the k=5 extension criterion. -/
theorem rankFour_k5_of_nonzero_target_in_range (E : Submodule (ZMod 2) K)
    (hE : Module.finrank (ZMod 2) E = 4)
    (hcoeff8 : (rootProduct (underlyingFinset E)).coeff 8 ≠ 0)
    (hrange : (rootProduct (underlyingFinset E)).coeff 8 ^ 2 ∈
      LinearMap.range (subspacePolynomialMap E)) :
    HasZeroSumSubspace K 5 := by
  obtain ⟨v, hv⟩ := hrange
  change (rootProduct (underlyingFinset E)).eval v = _ at hv
  have hvout : v ∉ E := by
    intro hmem
    have heval := (subspacePolynomial_eval_eq_zero_iff E v).mpr hmem
    rw [heval] at hv
    exact (pow_ne_zero 2 hcoeff8) hv.symm
  exact rankFour_extension_solution_gives_k5 E hE v hvout hv

/-- Under a nonzero coefficient, the rank-four extension equation has an
    outside solution exactly when its target lies in the linear-map image. -/
theorem rankFour_extension_point_iff_target_in_range
    (E : Submodule (ZMod 2) K)
    (hcoeff8 : (rootProduct (underlyingFinset E)).coeff 8 ≠ 0) :
    (∃ v : K, v ∉ E ∧ (rootProduct (underlyingFinset E)).eval v =
      ((rootProduct (underlyingFinset E)).coeff 8)^2) ↔
      (rootProduct (underlyingFinset E)).coeff 8 ^ 2 ∈
        LinearMap.range (subspacePolynomialMap E) := by
  constructor
  · rintro ⟨v, hvout, heval⟩
    exact ⟨v, heval⟩
  · intro hrange
    obtain ⟨v, hv⟩ := hrange
    change (rootProduct (underlyingFinset E)).eval v = _ at hv
    have hvout : v ∉ E := by
      intro hmem
      have heval := (subspacePolynomial_eval_eq_zero_iff E v).mpr hmem
      rw [heval] at hv
      exact (pow_ne_zero 2 hcoeff8) hv.symm
    exact ⟨v, hvout, hv⟩

/-- The rank-four subspace-polynomial map has image codimension four. -/
theorem subspacePolynomialMap_range_finrank (E : Submodule (ZMod 2) K) :
    Module.finrank (ZMod 2) (LinearMap.range (subspacePolynomialMap E)) +
      Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) K := by
  have h := LinearMap.finrank_range_add_finrank_ker (subspacePolynomialMap E)
  rw [subspacePolynomialMap_ker] at h
  exact h

/-- Membership in the rank-four linearized image can be tested by four trace
    equations against its trace-dual subspace. -/
theorem imageSubspace_mem_iff_dualImage_trace (E : Submodule (ZMod 2) K) (x : K) :
    x ∈ imageSubspace E ↔
      ∀ y ∈ dualImageEquiv E, Algebra.trace (ZMod 2) K (x*y) = 0 := by
  have horth : traceOrthogonal (dualImageEquiv E) = imageSubspace E := by
    change traceOrthogonal (traceOrthogonal (imageSubspace E)) = imageSubspace E
    exact traceOrthogonal_involutive (imageSubspace E)
  rw [← horth]
  change x ∈ (Algebra.traceForm (ZMod 2) K).orthogonal (dualImageEquiv E) ↔ _
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h y hy
    simpa [Algebra.traceForm, mul_comm] using h y hy
  · intro h y hy
    simpa [Algebra.traceForm, mul_comm] using h y hy

/-- Consequently, the rank-four extension target is in the image exactly when
    it is trace-orthogonal to the four-dimensional dual image. -/
theorem rankFour_target_in_range_iff_trace_tests (E : Submodule (ZMod 2) K) :
    (rootProduct (underlyingFinset E)).coeff 8 ^ 2 ∈
      LinearMap.range (subspacePolynomialMap E) ↔
    ∀ y ∈ dualImageEquiv E,
      Algebra.trace (ZMod 2) K
        ((rootProduct (underlyingFinset E)).coeff 8 ^ 2 * y) = 0 := by
  exact imageSubspace_mem_iff_dualImage_trace E _

#print axioms zeroSum_dualImage_iff_coeff16
#print axioms hasZeroSumSubspace_five_iff_exists_coeff16
#print axioms coeff_square_charTwo_pow
#print axioms coeff_subspaceExtension_pow
#print axioms rootProduct_sup_step_coeff_pow
#print axioms rootProduct_sup_step_coeff16_zero_iff
#print axioms rankFour_extend_zeroSumCoeff_iff
#print axioms rankFour_extension_solution_gives_k5
#print axioms rankFour_k5_of_nonzero_target_in_range
#print axioms rankFour_extension_point_iff_target_in_range
#print axioms subspacePolynomialMap_range_finrank
#print axioms imageSubspace_mem_iff_dualImage_trace
#print axioms rankFour_target_in_range_iff_trace_tests
end Carlet
