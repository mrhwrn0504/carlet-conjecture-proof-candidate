import Mathlib.Algebra.MvPolynomial.Eval
import Carlet.CandidatePaper.ReciprocalCoordinates

/-!
First finite-denominator bridge toward the localization evaluation map used by
the candidate paper's reciprocal-coordinate construction.

This file only proves that the common denominator formed from all nonzero
binary linear forms stays nonzero at a linearly independent tuple. It does not
yet construct the ring homomorphism from the reciprocal algebra.
-/

noncomputable section

namespace Carlet.CandidatePaper.ReciprocalLocalization

open MvPolynomial
open scoped BigOperators

abbrev BinaryVector (r : ℕ) := Fin r → ZMod 2

def nonzeroVectors (r : ℕ) : Finset (BinaryVector r) :=
  Finset.univ.erase 0

def commonLinearDenominator (r : ℕ) : MvPolynomial (Fin r) (ZMod 2) :=
  ∏ v ∈ nonzeroVectors r, Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v

theorem eval_commonLinearDenominator_ne_zero
    {r : ℕ} {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : Fin r → K) (hli : LinearIndependent (ZMod 2) x) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x (commonLinearDenominator r) ≠ 0 := by
  classical
  rw [commonLinearDenominator, MvPolynomial.eval₂_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  have hvne : v ≠ 0 := (Finset.mem_erase.mp hv).1
  exact Carlet.CandidatePaper.ReciprocalCoordinates.eval₂_linearForm_ne_zero x hli hvne

/-- The multiplicative generators that must be inverted to evaluate every
reciprocal coordinate. -/
def denominatorGenerators (r : ℕ) : Set (MvPolynomial (Fin r) (ZMod 2)) :=
  Set.range fun v : {v : Fin r → ZMod 2 // v ≠ 0} =>
    Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v

/-- Products of nonzero binary linear forms, including `1`. -/
def denominatorSubmonoid (r : ℕ) : Submonoid (MvPolynomial (Fin r) (ZMod 2)) :=
  Submonoid.closure (denominatorGenerators r)

/-- Every allowed localization denominator remains nonzero at a linearly
independent coordinate tuple. -/
theorem eval_denominator_ne_zero
    {r : ℕ} {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : Fin r → K) (hli : LinearIndependent (ZMod 2) x)
    {d : MvPolynomial (Fin r) (ZMod 2)}
    (hd : d ∈ denominatorSubmonoid r) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x d ≠ 0 := by
  classical
  induction hd using Submonoid.closure_induction with
  | mem p hp =>
      rcases hp with ⟨⟨v, hv⟩, rfl⟩
      exact Carlet.CandidatePaper.ReciprocalCoordinates.eval₂_linearForm_ne_zero x hli hv
  | one => simp
  | mul a b ha hb iha ihb =>
      simpa only [MvPolynomial.eval₂_mul] using mul_ne_zero iha ihb

/-- Every element of the denominator submonoid is a non-zero-divisor in the
polynomial ring. -/
theorem denominatorSubmonoid_le_nonZeroDivisors (r : ℕ) :
    denominatorSubmonoid r ≤ nonZeroDivisors (MvPolynomial (Fin r) (ZMod 2)) := by
  classical
  intro d hd
  rw [mem_nonZeroDivisors_iff_ne_zero]
  induction hd using Submonoid.closure_induction with
  | mem p hp =>
      rcases hp with ⟨⟨v, hv⟩, rfl⟩
      exact Carlet.CandidatePaper.ReciprocalCoordinates.linearForm_ne_zero hv
  | one => exact one_ne_zero
  | mul a b ha hb iha ihb => exact mul_ne_zero iha ihb

/-- The localization of the polynomial ring that adjoins inverses of all
nonzero binary linear forms. -/
abbrev ReciprocalLocalizationRing (r : ℕ) :=
  Localization (denominatorSubmonoid r)

theorem linearForm_mem_denominatorSubmonoid
    {r : ℕ} {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v ∈ denominatorSubmonoid r :=
  Submonoid.subset_closure ⟨⟨v, hv⟩, rfl⟩

theorem evalHom_units
    {r : ℕ} {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : Fin r → K) (hli : LinearIndependent (ZMod 2) x) :
    ∀ d : denominatorSubmonoid r,
      IsUnit ((MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K) x) d) := by
  intro d
  apply isUnit_iff_ne_zero.mpr
  change MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x (d : MvPolynomial (Fin r) (ZMod 2)) ≠ 0
  exact eval_denominator_ne_zero x hli d.property

/-- A full-rank coordinate tuple defines evaluation on the localization,
because every inverted linear form has nonzero value. -/
noncomputable def evalOnLocalization
    {r : ℕ} {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : Fin r → K) (hli : LinearIndependent (ZMod 2) x) :
    ReciprocalLocalizationRing r →+* K :=
  IsLocalization.lift (M := denominatorSubmonoid r)
    (g := MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K) x)
    (evalHom_units x hli)

/-- On the polynomial subring, localization evaluation agrees with ordinary
multivariate polynomial evaluation. -/
theorem evalOnLocalization_base
    {r : ℕ} {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : Fin r → K) (hli : LinearIndependent (ZMod 2) x)
    (p : MvPolynomial (Fin r) (ZMod 2)) :
    evalOnLocalization x hli (algebraMap _ (ReciprocalLocalizationRing r) p) =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x p := by
  exact IsLocalization.lift_eq
    (M := denominatorSubmonoid r)
    (g := MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K) x)
    (evalHom_units x hli) p

/-- The reciprocal coordinate represented by the localization fraction `1 / f`. -/
noncomputable def localizedReciprocal
    {r : ℕ} {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    ReciprocalLocalizationRing r :=
  IsLocalization.mk' (ReciprocalLocalizationRing r) 1
    ⟨Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v,
      linearForm_mem_denominatorSubmonoid hv⟩

/-- The localization embeds into the fraction field of the polynomial ring. -/
noncomputable def localizationToFraction (r : ℕ) :
    ReciprocalLocalizationRing r →+* Carlet.CandidatePaper.ReciprocalCoordinates.RationalFunctionField r :=
  IsLocalization.map (S := ReciprocalLocalizationRing r)
    (T := nonZeroDivisors (MvPolynomial (Fin r) (ZMod 2)))
    (Q := Carlet.CandidatePaper.ReciprocalCoordinates.RationalFunctionField r)
    (RingHom.id (MvPolynomial (Fin r) (ZMod 2)))
    (denominatorSubmonoid_le_nonZeroDivisors r)

theorem localizationToFraction_base
    (r : ℕ) (p : MvPolynomial (Fin r) (ZMod 2)) :
    localizationToFraction r
        (algebraMap (MvPolynomial (Fin r) (ZMod 2)) (ReciprocalLocalizationRing r) p) =
      algebraMap (MvPolynomial (Fin r) (ZMod 2))
        (Carlet.CandidatePaper.ReciprocalCoordinates.RationalFunctionField r) p := by
  exact IsLocalization.map_eq
    (S := ReciprocalLocalizationRing r)
    (Q := Carlet.CandidatePaper.ReciprocalCoordinates.RationalFunctionField r)
    (g := RingHom.id (MvPolynomial (Fin r) (ZMod 2)))
    (by
      intro d hd
      exact denominatorSubmonoid_le_nonZeroDivisors r hd)
    p

/-- The localized fraction `1 / L_v` maps to the reciprocal coordinate in the
fraction field used to define the manuscript's reciprocal algebra. -/
theorem localizationToFraction_reciprocal
    {r : ℕ} {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    localizationToFraction r (localizedReciprocal hv) =
      Carlet.CandidatePaper.ReciprocalCoordinates.reciprocalCoordinate r v := by
  have hspec := IsLocalization.mk'_spec (ReciprocalLocalizationRing r) (1 : MvPolynomial (Fin r) (ZMod 2))
    ⟨Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v,
      linearForm_mem_denominatorSubmonoid hv⟩
  have hmap := congrArg (localizationToFraction r) hspec
  rw [map_mul] at hmap
  rw [localizationToFraction_base] at hmap
  have hrec : localizationToFraction r (localizedReciprocal hv) =
      (algebraMap (MvPolynomial (Fin r) (ZMod 2))
        (Carlet.CandidatePaper.ReciprocalCoordinates.RationalFunctionField r)
        (Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [localizationToFraction, localizedReciprocal] using hmap
  simpa [Carlet.CandidatePaper.ReciprocalCoordinates.reciprocalCoordinate] using hrec

/-- Evaluation of the localized reciprocal coordinate agrees with the field
inverse used in the candidate paper. -/
theorem evalOnLocalization_reciprocal
    {r : ℕ} {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : Fin r → K) (hli : LinearIndependent (ZMod 2) x)
    {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    evalOnLocalization x hli (localizedReciprocal hv) =
      (MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x
        (Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v))⁻¹ := by
  have hspec := IsLocalization.mk'_spec (ReciprocalLocalizationRing r) (1 : MvPolynomial (Fin r) (ZMod 2))
    ⟨Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v,
      linearForm_mem_denominatorSubmonoid hv⟩
  have heval := congrArg (evalOnLocalization x hli) hspec
  rw [map_mul, evalOnLocalization_base, evalOnLocalization_base] at heval
  have heval' : evalOnLocalization x hli (localizedReciprocal hv) *
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x
        (Carlet.CandidatePaper.ReciprocalCoordinates.linearForm r v) = 1 := by
    simpa [localizedReciprocal] using heval
  exact eq_inv_of_mul_eq_one_left heval'

#print axioms eval_commonLinearDenominator_ne_zero
#print axioms eval_denominator_ne_zero
#print axioms denominatorSubmonoid_le_nonZeroDivisors
#print axioms evalHom_units
#print axioms evalOnLocalization
#print axioms evalOnLocalization_base
#print axioms localizedReciprocal
#print axioms localizationToFraction
#print axioms localizationToFraction_base
#print axioms localizationToFraction_reciprocal
#print axioms evalOnLocalization_reciprocal

end Carlet.CandidatePaper.ReciprocalLocalization
