import Carlet.CandidatePaper.Section32ReciprocalRingBridge

/-!
The candidate divisor section is a linear combination of degree-one reciprocal
coordinates. This file records that precise span statement independently of
claiming a full grading decomposition for the reciprocal subring.
-/

noncomputable section
namespace Carlet.CandidatePaper.Section31ReciprocalDegreeOne

open Carlet.CandidatePaper.Section32ReciprocalRingBridge

/-- The F₂-linear span of the reciprocal generators in the symmetric-algebra
fraction field. Once the grading is constructed, this is its degree-one piece. -/
def reciprocalGeneratorSpan (n : ℕ) :
    Submodule (ZMod 2) (CandidateSymmetricFractionField n) :=
  Submodule.span (ZMod 2) (candidateSymmetricReciprocalGenerators n)

theorem candidatePaperEll_mem_reciprocalGeneratorSpan (n : ℕ) :
    candidatePaperEllInSymmetricFractionField n ∈ reciprocalGeneratorSpan n := by
  classical
  unfold candidatePaperEllInSymmetricFractionField reciprocalGeneratorSpan
    candidateSymmetricReciprocalGenerators
  apply Submodule.sum_mem
  intro v hv
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  apply Submodule.subset_span
  exact ⟨⟨v, hv0⟩, rfl⟩

theorem candidatePaperEll_mem_generatorSpan_ne_zero (n : ℕ) (hn : 0 < n) :
    (⟨candidatePaperEllInSymmetricFractionField n,
      candidatePaperEll_mem_reciprocalGeneratorSpan n⟩ : reciprocalGeneratorSpan n) ≠ 0 := by
  intro hz
  have hval := congrArg Subtype.val hz
  exact candidatePaperEllInSymmetricFractionField_ne_zero n hn hval

#print axioms candidatePaperEll_mem_reciprocalGeneratorSpan
#print axioms candidatePaperEll_mem_generatorSpan_ne_zero

end Carlet.CandidatePaper.Section31ReciprocalDegreeOne
