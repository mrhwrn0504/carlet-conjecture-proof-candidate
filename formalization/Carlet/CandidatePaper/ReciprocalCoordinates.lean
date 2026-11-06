import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Localization.FractionRing
import Carlet.CandidatePaper.Section3

/-!
The first algebraic layer for the reciprocal compactification in the supplied
candidate paper. This file currently defines the universal linear forms and
proves that every nonzero F₂ coefficient vector gives a nonzero polynomial.
The graded reciprocal subring and its Proj are later obligations.
-/

noncomputable section

namespace Carlet.CandidatePaper.ReciprocalCoordinates

open MvPolynomial
open scoped BigOperators

/-- The linear form associated with a binary coefficient vector. -/
def linearForm (r : ℕ) (v : Fin r → ZMod 2) : MvPolynomial (Fin r) (ZMod 2) :=
  ∑ i : Fin r, C (v i) * X i

/-- A nonzero binary coefficient vector defines a nonzero linear polynomial. -/
theorem linearForm_ne_zero {r : ℕ} {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    linearForm r v ≠ 0 := by
  classical
  have hex : ∃ i : Fin r, v i ≠ 0 := by
    by_contra h
    have hzero : ∀ i : Fin r, v i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    apply hv
    funext i
    exact hzero i
  obtain ⟨i, hi⟩ := hex
  let e : Fin r → ZMod 2 := fun j => if j = i then 1 else 0
  have heval : MvPolynomial.eval e (linearForm r v) = v i := by
    simp [linearForm, e]
  intro hzero
  have hz : MvPolynomial.eval e (linearForm r v) = 0 := by
    rw [hzero]
    simp
  exact hi (heval.symm.trans hz)

/-- Rational function field containing all universal reciprocal coordinates. -/
abbrev RationalFunctionField (r : ℕ) :=
  FractionRing (MvPolynomial (Fin r) (ZMod 2))

/-- The reciprocal homogeneous coordinate indexed by a nonzero binary vector. -/
noncomputable def reciprocalCoordinate (r : ℕ) (v : Fin r → ZMod 2) :
    RationalFunctionField r :=
  (algebraMap (MvPolynomial (Fin r) (ZMod 2)) (RationalFunctionField r)
    (linearForm r v))⁻¹

/-- The image of a nonzero linear form remains nonzero in the fraction field. -/
theorem linearForm_fraction_ne_zero {r : ℕ} {v : Fin r → ZMod 2}
    (hv : v ≠ 0) :
    algebraMap (MvPolynomial (Fin r) (ZMod 2)) (RationalFunctionField r)
      (linearForm r v) ≠ 0 := by
  intro h
  have h' : algebraMap (MvPolynomial (Fin r) (ZMod 2)) (RationalFunctionField r)
      (linearForm r v) = algebraMap (MvPolynomial (Fin r) (ZMod 2))
        (RationalFunctionField r) (0 : MvPolynomial (Fin r) (ZMod 2)) := by
    simpa using h
  exact linearForm_ne_zero hv ((IsFractionRing.injective _ _) h')

/-- Multiplication by the corresponding linear form cancels its reciprocal
coordinate in the rational function field. -/
theorem reciprocalCoordinate_mul_linearForm {r : ℕ} {v : Fin r → ZMod 2}
    (hv : v ≠ 0) :
    reciprocalCoordinate r v *
      algebraMap (MvPolynomial (Fin r) (ZMod 2)) (RationalFunctionField r)
        (linearForm r v) = 1 := by
  rw [reciprocalCoordinate]
  exact inv_mul_cancel₀ (linearForm_fraction_ne_zero hv)

/-- The ungraded reciprocal coordinate algebra inside the rational function
field. The projective compactification requires the additional grading, which
is intentionally not asserted here. -/
def reciprocalGenerators (r : ℕ) : Set (RationalFunctionField r) :=
  Set.range (fun v : {v : Fin r → ZMod 2 // v ≠ 0} => reciprocalCoordinate r v)

def reciprocalSubalgebra (r : ℕ) :
    Subalgebra (ZMod 2) (RationalFunctionField r) :=
  Algebra.adjoin (ZMod 2) (reciprocalGenerators r)

theorem reciprocalCoordinate_mem_subalgebra {r : ℕ} {v : Fin r → ZMod 2}
    (hv : v ≠ 0) : reciprocalCoordinate r v ∈ reciprocalSubalgebra r := by
  apply Algebra.subset_adjoin
  exact ⟨⟨v, hv⟩, rfl⟩

/-- Evaluation of a universal linear form at an F₂-linear coordinate tuple is
the corresponding binary linear combination. -/
theorem eval₂_linearForm {r : ℕ} {K : Type*} [CommRing K]
    [Algebra (ZMod 2) K] (x : Fin r → K) (v : Fin r → ZMod 2) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x (linearForm r v) =
      ∑ i : Fin r, v i • x i := by
  simp [linearForm, Algebra.smul_def]

/-- Linear independence guarantees that every nonzero reciprocal denominator
survives evaluation at the corresponding full-rank affine point. -/
theorem eval₂_linearForm_ne_zero {r : ℕ} {K : Type*} [Field K]
    [Algebra (ZMod 2) K] (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x (linearForm r v) ≠ 0 := by
  rw [eval₂_linearForm]
  intro hsum
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) v hsum
  exact hv (funext hcoeff)

/-- Every reciprocal denominator is nonzero when evaluated at a manuscript
open point, because its coordinates are linearly independent. -/
theorem eval₂_linearForm_ne_zero_of_openPoint {r : ℕ} {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (y : Carlet.Quadratic.OpenCarletPoint K r)
    {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) y.val (linearForm r v) ≠ 0 := by
  exact eval₂_linearForm_ne_zero y.val
    (Carlet.CandidatePaper.Section3.openPoint_coordinates_linearIndependent r y) hv

/-- The value assigned to a reciprocal generator at a full-rank affine point. -/
def reciprocalGeneratorValue {r : ℕ} {K : Type*} [Field K]
    [Algebra (ZMod 2) K] (x : Fin r → K) (v : Fin r → ZMod 2) : K :=
  Ring.inverse (MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x (linearForm r v))

theorem reciprocalGeneratorValue_mul_denominator {r : ℕ} {K : Type*}
    [Field K] [Algebra (ZMod 2) K] (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) {v : Fin r → ZMod 2} (hv : v ≠ 0) :
    reciprocalGeneratorValue x v *
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) x (linearForm r v) = 1 := by
  exact Ring.inverse_mul_cancel _
    (isUnit_iff_ne_zero.mpr (eval₂_linearForm_ne_zero x hli hv))

#print axioms linearForm_ne_zero
#print axioms linearForm_fraction_ne_zero
#print axioms reciprocalCoordinate_mul_linearForm
#print axioms reciprocalCoordinate_mem_subalgebra
#print axioms eval₂_linearForm
#print axioms eval₂_linearForm_ne_zero
#print axioms eval₂_linearForm_ne_zero_of_openPoint
#print axioms reciprocalGeneratorValue_mul_denominator

end Carlet.CandidatePaper.ReciprocalCoordinates
