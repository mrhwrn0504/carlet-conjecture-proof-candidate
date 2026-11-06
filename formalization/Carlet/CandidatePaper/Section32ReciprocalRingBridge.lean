import Carlet.CandidatePaper.Section32GenericReciprocalInduction
import Carlet.CandidatePaper.ReciprocalCoordinates
import Carlet.CandidatePaper.Section31SymmetricAlgebraBridge
import Mathlib.RingTheory.Localization.FractionRing

/-!
This module identifies the generic Section 3.2 reciprocal sum with the
reciprocal coordinates/subalgebra introduced for Section 3.1. It removes a
parallel model and certifies that the manuscript's sum is a nonzero element of
the exact ungraded reciprocal subalgebra.
-/

noncomputable section

namespace Carlet.CandidatePaper.Section32ReciprocalRingBridge

open scoped BigOperators
open Carlet.CandidatePaper.Section32GenericCoordinateField
open Carlet.CandidatePaper.Section32GenericReciprocalInduction
open Carlet.CandidatePaper.Section32CoordinateSplit
open Carlet.CandidatePaper.ReciprocalCoordinates
open Carlet.CandidatePaper.Section31SymmetricAlgebraBridge

theorem linearForm_eq_genericCoordinate_form (n : ℕ) (v : Fin n → ZMod 2) :
    algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalField n) (linearForm n v) =
      binaryLinearForm (genericCoordinate n) v := by
  unfold linearForm binaryLinearForm genericCoordinate
  rw [MvPolynomial.C_eq_algebraMap]
  simp only [map_sum, map_mul, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(IsScalarTower.algebraMap_apply (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))
    (RationalField n) (v i)).symm]

theorem reciprocalCoordinate_eq_genericForm_inv (n : ℕ) (v : Fin n → ZMod 2) :
    (binaryLinearForm (genericCoordinate n) v)⁻¹ = reciprocalCoordinate n v := by
  unfold reciprocalCoordinate
  rw [← linearForm_eq_genericCoordinate_form]

/-- The manuscript's reciprocal ring, reusing the existing coordinate model. -/
def candidatePaperReciprocalSubring (n : ℕ) :
    Subalgebra (ZMod 2) (RationalField n) := reciprocalSubalgebra n

/-- The finite reciprocal sum from the candidate manuscript belongs to its
reciprocal subring. -/
theorem candidatePaperEll_mem_reciprocalSubring (n : ℕ) :
    candidatePaperEll n ∈ candidatePaperReciprocalSubring n := by
  classical
  unfold candidatePaperEll candidatePaperReciprocalSubring
  apply Subalgebra.sum_mem
  intro v hv
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1

  rw [reciprocalCoordinate_eq_genericForm_inv]
  exact reciprocalCoordinate_mem_subalgebra hv0

/-- The manuscript's section as an element of its generated reciprocal ring. -/
def candidatePaperEllElement (n : ℕ) : candidatePaperReciprocalSubring n :=
  ⟨candidatePaperEll n, candidatePaperEll_mem_reciprocalSubring n⟩

theorem candidatePaperEllElement_ne_zero (n : ℕ) (hn : 0 < n) :
    candidatePaperEllElement n ≠ 0 := by
  intro hz
  apply candidatePaperEll_nonzero n hn
  exact congrArg Subtype.val hz

abbrev CandidateSymmetricAlgebra (n : ℕ) :=
  SymmetricAlgebra (ZMod 2) (BinaryVector n)
abbrev CandidateSymmetricFractionField (n : ℕ) :=
  FractionRing (CandidateSymmetricAlgebra n)

def symmetricFractionEquiv (n : ℕ) :
    CandidateSymmetricFractionField n ≃+* RationalField n :=
  IsFractionRing.ringEquivOfRingEquiv (symmetricPolynomialEquiv n).toRingEquiv

theorem symmetricFractionEquiv_ι (n : ℕ) (v : BinaryVector n) :
    symmetricFractionEquiv n (algebraMap (CandidateSymmetricAlgebra n)
      (CandidateSymmetricFractionField n)
      (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v)) =
      algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalField n)
        (linearForm n v) := by
  rw [symmetricFractionEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalField n)
    (symmetricPolynomialEquiv n (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v)) = _
  rw [symmetricAlgebra_vector_eq_linearForm]

def candidatePaperEllInSymmetricFractionField (n : ℕ) :
    CandidateSymmetricFractionField n :=
  ∑ v ∈ (Finset.univ : Finset (BinaryVector n)).erase 0,
    (algebraMap (CandidateSymmetricAlgebra n)
      (CandidateSymmetricFractionField n)
      (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v))⁻¹

theorem symmetricFractionEquiv_candidatePaperEll (n : ℕ) :
    symmetricFractionEquiv n (candidatePaperEllInSymmetricFractionField n) =
      candidatePaperEll n := by
  classical
  unfold candidatePaperEllInSymmetricFractionField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_inv₀, symmetricFractionEquiv_ι]
  rw [linearForm_eq_genericCoordinate_form]


theorem candidatePaperEllInSymmetricFractionField_ne_zero
    (n : ℕ) (hn : 0 < n) :
    candidatePaperEllInSymmetricFractionField n ≠ 0 := by
  intro hz
  have hmap := congrArg (symmetricFractionEquiv n) hz
  rw [map_zero, symmetricFractionEquiv_candidatePaperEll] at hmap
  exact candidatePaperEll_nonzero n hn hmap
theorem symmetricAlgebra_vector_ne_zero {n : ℕ} {v : BinaryVector n}
    (hv : v ≠ 0) : SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v ≠ 0 := by
  intro hz
  have hp := congrArg (symmetricPolynomialEquiv n) hz
  rw [map_zero, symmetricAlgebra_vector_eq_linearForm] at hp
  exact linearForm_ne_zero hv hp

theorem symmetricVector_fraction_ne_zero {n : ℕ} {v : BinaryVector n}
    (hv : v ≠ 0) :
    algebraMap (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n)
      (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v) ≠ 0 := by
  intro hz
  apply symmetricAlgebra_vector_ne_zero hv
  exact (IsFractionRing.injective (CandidateSymmetricAlgebra n)
    (CandidateSymmetricFractionField n)) (by simpa using hz)

def candidateSymmetricReciprocalGenerators (n : ℕ) :
    Set (CandidateSymmetricFractionField n) :=
  Set.range (fun v : {u : BinaryVector n // u ≠ 0} =>
    (algebraMap (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n)
      (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v.1))⁻¹)

def candidateSymmetricReciprocalSubring (n : ℕ) :
    Subalgebra (ZMod 2) (CandidateSymmetricFractionField n) :=
  Algebra.adjoin (ZMod 2) (candidateSymmetricReciprocalGenerators n)

theorem candidatePaperEllInSymmetricFractionField_mem_subring (n : ℕ) :
    candidatePaperEllInSymmetricFractionField n ∈
      candidateSymmetricReciprocalSubring n := by
  classical
  unfold candidatePaperEllInSymmetricFractionField candidateSymmetricReciprocalSubring
    candidateSymmetricReciprocalGenerators
  apply Subalgebra.sum_mem
  intro v hv
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  apply Algebra.subset_adjoin
  exact ⟨⟨v, hv0⟩, rfl⟩

def candidatePaperEllInSymmetricReciprocalSubring (n : ℕ) :
    candidateSymmetricReciprocalSubring n :=
  ⟨candidatePaperEllInSymmetricFractionField n,
    candidatePaperEllInSymmetricFractionField_mem_subring n⟩

theorem candidatePaperEllInSymmetricReciprocalSubring_ne_zero
    (n : ℕ) (hn : 0 < n) :
    candidatePaperEllInSymmetricReciprocalSubring n ≠ 0 := by
  intro hz
  have hval := congrArg Subtype.val hz
  exact candidatePaperEllInSymmetricFractionField_ne_zero n hn hval
#print axioms linearForm_eq_genericCoordinate_form
#print axioms reciprocalCoordinate_eq_genericForm_inv
#print axioms candidatePaperEll_mem_reciprocalSubring
#print axioms candidatePaperEllElement_ne_zero
#print axioms symmetricFractionEquiv_ι
#print axioms symmetricFractionEquiv_candidatePaperEll
#print axioms candidatePaperEllInSymmetricFractionField_ne_zero
#print axioms symmetricAlgebra_vector_ne_zero
#print axioms symmetricVector_fraction_ne_zero
#print axioms candidatePaperEllInSymmetricFractionField_mem_subring
#print axioms candidatePaperEllInSymmetricReciprocalSubring_ne_zero

end Carlet.CandidatePaper.Section32ReciprocalRingBridge
