import Carlet.CandidatePaper.Section31ReciprocalPresentation
import Carlet.CandidatePaper.ReciprocalCoordinates
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! A common homogeneous denominator for the reciprocal presentation. -/

noncomputable section
namespace Carlet.CandidatePaper.Section31ReciprocalCommonDenominator

open Carlet.CandidatePaper.ReciprocalCoordinates
open Carlet.CandidatePaper.Section31SymmetricAlgebraBridge
open Carlet.CandidatePaper.Section31ReciprocalPresentation
open scoped BigOperators

def nonzeroVectors (n : ℕ) : Finset (BinaryVector n) :=
  (Finset.univ : Finset (BinaryVector n)).erase 0

def commonDenominator (n : ℕ) : MvPolynomial (Fin n) (ZMod 2) :=
  ∏ v ∈ nonzeroVectors n, linearForm n v

def denominatorComplement (n : ℕ) (v : BinaryVector n) :
    MvPolynomial (Fin n) (ZMod 2) :=
  ∏ w ∈ (nonzeroVectors n).erase v, linearForm n w

theorem linearForm_isHomogeneous_one (n : ℕ) (v : BinaryVector n) :
    (linearForm n v).IsHomogeneous 1 := by
  classical
  unfold linearForm
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_C_mul_X (v i) i

theorem commonDenominator_isHomogeneous (n : ℕ) :
    (commonDenominator n).IsHomogeneous (nonzeroVectors n).card := by
  classical
  unfold commonDenominator
  have hprod := MvPolynomial.IsHomogeneous.prod (nonzeroVectors n)
    (fun v => linearForm n v) (fun _ => 1)
    (by
      intro v hv
      exact linearForm_isHomogeneous_one n v)
  simpa using hprod

theorem denominatorComplement_isHomogeneous (n : ℕ) (v : BinaryVector n) :
    (denominatorComplement n v).IsHomogeneous ((nonzeroVectors n).erase v).card := by
  classical
  unfold denominatorComplement
  have hprod := MvPolynomial.IsHomogeneous.prod ((nonzeroVectors n).erase v)
    (fun w => linearForm n w) (fun _ => 1)
    (by
      intro w hw
      exact linearForm_isHomogeneous_one n w)
  simpa using hprod

theorem denominatorComplement_nonzero (n : ℕ) (v : BinaryVector n) :
    denominatorComplement n v ≠ 0 := by
  classical
  unfold denominatorComplement
  apply Finset.prod_ne_zero_iff.mpr
  intro w hw
  exact linearForm_ne_zero ((Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1)

theorem commonDenominator_nonzero (n : ℕ) : commonDenominator n ≠ 0 := by
  classical
  unfold commonDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact linearForm_ne_zero ((Finset.mem_erase.mp hv).1)

theorem commonDenominator_factor (n : ℕ) (v : BinaryVector n)
    (hv : v ∈ nonzeroVectors n) :
    commonDenominator n = denominatorComplement n v * linearForm n v := by
  classical
  unfold commonDenominator denominatorComplement
  exact (Finset.prod_erase_mul (nonzeroVectors n) (fun w => linearForm n w) hv).symm

theorem denominatorComplement_eq_common_mul_reciprocal (n : ℕ) (v : BinaryVector n)
    (hv : v ∈ nonzeroVectors n) :
    algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
        (denominatorComplement n v) =
      algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
        (commonDenominator n) * reciprocalCoordinate n v := by
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  rw [commonDenominator_factor n v hv, map_mul]
  simp [reciprocalCoordinate, linearForm_fraction_ne_zero hv0]

def denominatorScaledGenerator (n : ℕ) (v : BinaryVector n) :
    MvPolynomial (Fin n) (ZMod 2) :=
  if v = 0 then 0 else denominatorComplement n v

def denominatorScaledEvaluation (n : ℕ) :
    reciprocalPolynomial n →ₐ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  MvPolynomial.aeval (denominatorScaledGenerator n)

theorem denominatorScaledGenerator_isHomogeneous (n : ℕ) (v : BinaryVector n) :
    (denominatorScaledGenerator n v).IsHomogeneous ((nonzeroVectors n).card - 1) := by
  by_cases hv : v = 0
  · simp [denominatorScaledGenerator, hv, MvPolynomial.isHomogeneous_zero]
  · have hvset : v ∈ nonzeroVectors n := by
      simp [nonzeroVectors, hv]
    rw [denominatorScaledGenerator, if_neg hv]
    simpa [Finset.card_erase_of_mem hvset] using denominatorComplement_isHomogeneous n v

theorem denominatorScaledEvaluation_preservesHomogeneity (n : ℕ)
    {p : reciprocalPolynomial n} {d : ℕ} (hp : p.IsHomogeneous d) :
    (denominatorScaledEvaluation n p).IsHomogeneous (((nonzeroVectors n).card - 1) * d) := by
  exact MvPolynomial.IsHomogeneous.aeval hp (denominatorScaledGenerator n)
    (denominatorScaledGenerator_isHomogeneous n)

def genericReciprocalEvaluation (n : ℕ) :
    reciprocalPolynomial n →ₐ[ZMod 2] RationalFunctionField n :=
  MvPolynomial.aeval (fun v : BinaryVector n =>
    if v = 0 then 0 else reciprocalCoordinate n v)

def commonDenominatorInField (n : ℕ) : RationalFunctionField n :=
  algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
    (commonDenominator n)

theorem denominatorScaledEvaluation_toFraction_eq (n : ℕ) :
    (algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)).comp
        (denominatorScaledEvaluation n).toRingHom =
      (MvPolynomial.aeval (fun v : BinaryVector n =>
        commonDenominatorInField n * (if v = 0 then 0 else reciprocalCoordinate n v))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
        (denominatorScaledEvaluation n (MvPolynomial.C c)) =
      MvPolynomial.aeval (fun v : BinaryVector n =>
        commonDenominatorInField n * (if v = 0 then 0 else reciprocalCoordinate n v))
        (MvPolynomial.C c)
    simp only [denominatorScaledEvaluation, MvPolynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply (ZMod 2)
      (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n) c).symm
  · intro v
    change algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
        (denominatorScaledEvaluation n (MvPolynomial.X v)) =
      MvPolynomial.aeval (fun v : BinaryVector n =>
        commonDenominatorInField n * (if v = 0 then 0 else reciprocalCoordinate n v))
        (MvPolynomial.X v)
    simp only [denominatorScaledEvaluation, MvPolynomial.aeval_X]
    by_cases hv : v = 0
    · simp [denominatorScaledGenerator, hv]
    · have hvset : v ∈ nonzeroVectors n := by
        simp [nonzeroVectors, hv]
      rw [denominatorScaledGenerator, if_neg hv]
      simpa [commonDenominatorInField, hv] using
        denominatorComplement_eq_common_mul_reciprocal n v hvset

theorem denominatorScaledEvaluation_field_eq_of_isHomogeneous (n : ℕ)
    {p : reciprocalPolynomial n} {d : ℕ} (hp : p.IsHomogeneous d) :
    algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
        (denominatorScaledEvaluation n p) =
      (commonDenominatorInField n) ^ d * genericReciprocalEvaluation n p := by
  have hscaled := congrArg (fun f : MvPolynomial (BinaryVector n) (ZMod 2) →+*
      RationalFunctionField n => f p) (denominatorScaledEvaluation_toFraction_eq n)
  change algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
      (denominatorScaledEvaluation n p) =
    (MvPolynomial.aeval (fun v : BinaryVector n =>
      commonDenominatorInField n * (if v = 0 then 0 else reciprocalCoordinate n v))) p at hscaled
  rw [hscaled]
  simpa [commonDenominatorInField, genericReciprocalEvaluation] using
    (aeval_smul_of_isHomogeneous (commonDenominatorInField n)
      (fun v : BinaryVector n => if v = 0 then 0 else reciprocalCoordinate n v) hp)

#print axioms linearForm_isHomogeneous_one
#print axioms commonDenominator_isHomogeneous
#print axioms denominatorComplement_isHomogeneous
#print axioms denominatorComplement_nonzero
#print axioms commonDenominator_nonzero
#print axioms commonDenominator_factor
#print axioms denominatorComplement_eq_common_mul_reciprocal
#print axioms denominatorScaledGenerator_isHomogeneous
#print axioms denominatorScaledEvaluation_preservesHomogeneity
#print axioms denominatorScaledEvaluation_toFraction_eq
#print axioms denominatorScaledEvaluation_field_eq_of_isHomogeneous

end Carlet.CandidatePaper.Section31ReciprocalCommonDenominator
