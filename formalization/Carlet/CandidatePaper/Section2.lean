import Carlet.SubspacePolynomial

/-!
Paper-specific interface for Section 2 of the supplied Carlet proof candidate.

These declarations state the manuscript's reciprocal-sum criterion, extension
identity, and last-step solver using the exact finite-field and subspace objects
in `Carlet.Statement`.  The proofs are the Lean theorems imported below; this
file does not assert that later geometric sections of the manuscript have been
formalized.
-/

noncomputable section

namespace Carlet.CandidatePaper.Section2

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

/-- Candidate paper Lemma 2.2: the reciprocal sum vanishes exactly when the
`X²` coefficient of the subspace root polynomial vanishes. -/
theorem lemma_2_2_reciprocal_sum (E : Submodule (ZMod 2) K) :
    IsZeroSum E ↔ (rootProduct (underlyingFinset E)).coeff 2 = 0 :=
  zeroSum_iff_coeff_two E

/-- Candidate paper Lemma 2.3: adjoining one independent vector gives the
stated root-polynomial recurrence. -/
theorem lemma_2_3_extension [DecidableEq K] (E : Submodule (ZMod 2) K) (v : K)
    (hv : v ∉ E) :
    rootProduct (underlyingFinset (E ⊔ Submodule.span (ZMod 2) ({v} : Set K))) =
      rootProduct (underlyingFinset E) ^ 2 +
        C ((rootProduct (underlyingFinset E)).eval v) *
          rootProduct (underlyingFinset E) :=
  subspacePolynomial_extension E v hv

/-- Candidate paper Corollary 2.4: the final extension is zero-sum precisely
when the evaluation hits the coefficient-ratio target. -/
theorem corollary_2_4_extension_solver [DecidableEq K] (E : Submodule (ZMod 2) K) (v : K)
    (hv : v ∉ E)
    (h₂ : (rootProduct (underlyingFinset E)).coeff 2 ≠ 0) :
    IsZeroSum (E ⊔ Submodule.span (ZMod 2) ({v} : Set K)) ↔
      (rootProduct (underlyingFinset E)).eval v =
        (rootProduct (underlyingFinset E)).coeff 1 ^ 2 /
          (rootProduct (underlyingFinset E)).coeff 2 :=
  extension_zeroSum_iff E v hv h₂

/-- Candidate paper's existence reduction: once the target is in the image of
the subspace-polynomial map, the manuscript's one-dimensional extension is a
zero-sum subspace of the claimed dimension. -/
theorem final_step_solver [DecidableEq K] (E : Submodule (ZMod 2) K)
    (h₂ : (rootProduct (underlyingFinset E)).coeff 2 ≠ 0)
    (himage : (rootProduct (underlyingFinset E)).coeff 1 ^ 2 /
        (rootProduct (underlyingFinset E)).coeff 2 ∈
          LinearMap.range (subspacePolynomialMap E)) :
    HasZeroSumSubspace K (Module.finrank (ZMod 2) E + 1) :=
  solver_yields_zeroSum_subspace E h₂ himage

#print axioms lemma_2_2_reciprocal_sum
#print axioms lemma_2_3_extension
#print axioms corollary_2_4_extension_solver
#print axioms final_step_solver

end Carlet.CandidatePaper.Section2
