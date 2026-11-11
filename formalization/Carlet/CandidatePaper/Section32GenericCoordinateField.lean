import Carlet.CandidatePaper.Section32InfiniteFiber
import Carlet.CandidatePaper.Section32IntegralDomainFiber
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
This file realizes the generic binary coordinates as algebraically independent
variables in multivariate rational function fields. It is the algebraic
coordinate-field interface needed to specialize Section 3.2's abstract fiber
identity. The identification of the rational function field over `FR n` with
`FR (n+1)` is handled separately.
-/

noncomputable section

namespace Carlet.CandidatePaper.Section32GenericCoordinateField

open MvPolynomial

abbrev PolyFieldBase (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)
abbrev RationalField (n : ℕ) := FractionRing (PolyFieldBase n)

/-- Cyclically move the last coordinate to index zero and shift all preceding
coordinates to successor indices. This aligns `finSuccEquiv` with our
last-coordinate extension convention. -/
def cyclicLastToZero (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun i := Fin.lastCases 0 (fun j => Fin.succAbove (0 : Fin (n + 1)) j) i
  invFun i := Fin.cases (Fin.last n) (fun j => Fin.castSucc j) i
  left_inv := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succAbove]
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.succAbove]
    · simp [Fin.succAbove]

/-- The coordinate polynomial ring in one extra variable is canonically a
single-variable polynomial ring over the old coordinate ring. -/
noncomputable def finSuccPolynomialEquiv (n : ℕ) :
    PolyFieldBase (n + 1) ≃ₐ[ZMod 2] Polynomial (PolyFieldBase n) :=
  (MvPolynomial.renameEquiv (ZMod 2) (cyclicLastToZero n)).trans
    (MvPolynomial.finSuccEquiv (ZMod 2) n)

theorem finSuccPolynomialEquiv_old (n : ℕ) (i : Fin n) :
    finSuccPolynomialEquiv n (MvPolynomial.X i.castSucc) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [finSuccPolynomialEquiv, cyclicLastToZero, MvPolynomial.renameEquiv,
    MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ, Fin.succAbove]

theorem finSuccPolynomialEquiv_new (n : ℕ) :
    finSuccPolynomialEquiv n (MvPolynomial.X (Fin.last n)) = Polynomial.X := by
  simp [finSuccPolynomialEquiv, cyclicLastToZero, MvPolynomial.renameEquiv,
    MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero, Fin.succAbove]

/-- The finite-coordinate polynomial equivalence extends to an embedding of
its rational function field into the next generic-coordinate field. -/
def finSuccFractionFieldMap (n : ℕ) :
    FractionRing (Polynomial (PolyFieldBase n)) →+* RationalField (n + 1) :=
  IsFractionRing.map (j := (finSuccPolynomialEquiv n).symm.toRingHom)
    ((finSuccPolynomialEquiv n).symm.injective)

def polynomialRename (n : ℕ) : PolyFieldBase n →+* PolyFieldBase (n + 1) :=
  (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom

theorem polynomialRename_injective (n : ℕ) :
    Function.Injective (polynomialRename n) := by
  apply MvPolynomial.rename_injective
  exact Fin.castSucc_injective n

def rationalFieldMap (n : ℕ) : RationalField n →+* RationalField (n + 1) :=
  IsFractionRing.map (polynomialRename_injective n)

local instance (priority := 2000) rationalFieldAlgebra (n : ℕ) :
    Algebra (RationalField n) (RationalField (n + 1)) :=
  (rationalFieldMap n).toAlgebra

theorem algebraMap_eq_rationalFieldMap (n : ℕ) :
    algebraMap (RationalField n) (RationalField (n + 1)) = rationalFieldMap n := by
  rfl

theorem rationalFieldMap_base (n : ℕ) :
    (rationalFieldMap n).comp (algebraMap (ZMod 2) (RationalField n)) =
      algebraMap (ZMod 2) (RationalField (n + 1)) := by
  rw [IsScalarTower.algebraMap_eq (ZMod 2) (PolyFieldBase n) (RationalField n)]
  rw [IsScalarTower.algebraMap_eq (ZMod 2) (PolyFieldBase (n + 1))
    (RationalField (n + 1))]
  ext a
  simp only [RingHom.comp_apply]
  rw [rationalFieldMap, IsFractionRing.map, IsLocalization.map_eq]
  simp [polynomialRename]

local instance (n : ℕ) : IsScalarTower (ZMod 2) (RationalField n)
    (RationalField (n + 1)) where
  smul_assoc a b c := by
    simp only [Algebra.smul_def, algebraMap_eq_rationalFieldMap]
    rw [map_mul]
    have ha : rationalFieldMap n (algebraMap (ZMod 2) (RationalField n) a) =
        algebraMap (ZMod 2) (RationalField (n + 1)) a := by
      have h := congrArg (fun f : ZMod 2 →+* RationalField (n + 1) => f a)
        (rationalFieldMap_base n)
      simpa [RingHom.comp_apply] using h
    rw [ha]
    ring

def genericCoordinate (n : ℕ) : Fin n → RationalField n := fun i =>
  algebraMap (PolyFieldBase n) (RationalField n) (MvPolynomial.X i)

theorem finSuccFractionFieldMap_injective (n : ℕ) :
    Function.Injective (finSuccFractionFieldMap n) :=
  RingHom.injective (finSuccFractionFieldMap n)

theorem finSuccFractionFieldMap_old (n : ℕ) (i : Fin n) :
    finSuccFractionFieldMap n
        (algebraMap (Polynomial (PolyFieldBase n))
          (FractionRing (Polynomial (PolyFieldBase n))) (Polynomial.C (MvPolynomial.X i))) =
      genericCoordinate (n + 1) i.castSucc := by
  simp only [finSuccFractionFieldMap, IsFractionRing.map, IsLocalization.map_eq]
  rw [← finSuccPolynomialEquiv_old n i]
  simp [genericCoordinate]

theorem finSuccFractionFieldMap_new (n : ℕ) :
    finSuccFractionFieldMap n
        (algebraMap (Polynomial (PolyFieldBase n))
          (FractionRing (Polynomial (PolyFieldBase n))) Polynomial.X) =
      genericCoordinate (n + 1) (Fin.last n) := by
  simp only [finSuccFractionFieldMap, IsFractionRing.map, IsLocalization.map_eq]
  rw [← finSuccPolynomialEquiv_new n]
  simp [genericCoordinate]

theorem genericCoordinates_linearIndependent (n : ℕ) :
    LinearIndependent (ZMod 2) (genericCoordinate n) := by
  rw [Fintype.linearIndependent_iff]
  intro a hsum i
  have hpoly : algebraMap (PolyFieldBase n) (RationalField n)
      (∑ j, a j • MvPolynomial.X j) = 0 := by
    rw [map_sum]
    have hterm (j : Fin n) :
        algebraMap (PolyFieldBase n) (RationalField n)
            (a j • MvPolynomial.X j) = a j • genericCoordinate n j := by
      calc
        algebraMap (PolyFieldBase n) (RationalField n)
            (a j • MvPolynomial.X j) =
            algebraMap (PolyFieldBase n) (RationalField n)
              (algebraMap (ZMod 2) (PolyFieldBase n) (a j) * MvPolynomial.X j) := by
                rw [Algebra.smul_def]
        _ = algebraMap (PolyFieldBase n) (RationalField n)
              (algebraMap (ZMod 2) (PolyFieldBase n) (a j)) *
              algebraMap (PolyFieldBase n) (RationalField n) (MvPolynomial.X j) :=
                map_mul _ _ _
        _ = algebraMap (ZMod 2) (RationalField n) (a j) * genericCoordinate n j := by
              rw [← IsScalarTower.algebraMap_apply]
              rfl
        _ = a j • genericCoordinate n j := by rw [Algebra.smul_def]
    simpa [hterm, genericCoordinate] using hsum
  have hpoly0 : (∑ j : Fin n, a j • (MvPolynomial.X j : PolyFieldBase n)) =
      (0 : PolyFieldBase n) := by
    apply (IsFractionRing.injective (PolyFieldBase n) (RationalField n))
    simpa using hpoly
  have hx := MvPolynomial.linearIndependent_X (Fin n) (ZMod 2)
  exact (Fintype.linearIndependent_iff.mp hx) a hpoly0 i

/-- The canonical embedding of rational-function fields sends each old
coordinate to the corresponding `castSucc` coordinate in the larger field. -/
theorem rationalFieldMap_genericCoordinate (n : ℕ) (i : Fin n) :
    rationalFieldMap n (genericCoordinate n i) =
      genericCoordinate (n + 1) i.castSucc := by
  rw [genericCoordinate, genericCoordinate, rationalFieldMap, IsFractionRing.map,
    IsLocalization.map_eq]
  simp [polynomialRename]

/-- The Section 3.2 reciprocal sum commutes with the canonical inclusion of
successive generic-coordinate rational-function fields. -/
theorem genericReciprocalSum_map (n : ℕ) :
    rationalFieldMap n
        (Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) =
      Section32CoordinateSplit.binaryReciprocalSum
        (fun i : Fin n => genericCoordinate (n + 1) i.castSucc) := by
  rw [← algebraMap_eq_rationalFieldMap n]
  rw [Section32InfiniteFiber.binaryReciprocalSum_algebraMap]
  apply congrArg Section32CoordinateSplit.binaryReciprocalSum
  funext i
  exact rationalFieldMap_genericCoordinate n i

/-- The map from the polynomial fraction field evaluates polynomial-ring
representatives through the coordinate-field equivalence. -/
theorem finSuccFractionFieldMap_algebraMap (n : ℕ)
    (p : Polynomial (PolyFieldBase n)) :
    finSuccFractionFieldMap n
      (algebraMap (Polynomial (PolyFieldBase n))
        (FractionRing (Polynomial (PolyFieldBase n))) p) =
      algebraMap (PolyFieldBase (n + 1)) (RationalField (n + 1))
        ((finSuccPolynomialEquiv n).symm p) := by
  simp only [finSuccFractionFieldMap, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem rationalFieldMap_algebraMap (n : ℕ) (p : PolyFieldBase n) :
    rationalFieldMap n (algebraMap (PolyFieldBase n) (RationalField n) p) =
      algebraMap (PolyFieldBase (n + 1)) (RationalField (n + 1))
        (polynomialRename n p) := by
  simp only [rationalFieldMap, IsFractionRing.map, IsLocalization.map_eq]

/-- The coefficient-field inclusion followed by the last-coordinate
polynomial fraction map is exactly the canonical inclusion of rational
function fields. This is the bridge needed to transport the finite-fiber
noncancellation theorem to generic coordinates. -/
theorem finSuccFractionFieldMap_comp_coeffMap (n : ℕ) :
    (finSuccFractionFieldMap n).comp
        (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
          (R := PolyFieldBase n)) =
      rationalFieldMap n := by
  apply IsFractionRing.ringHom_ext (A := PolyFieldBase n)
  intro p
  have hpoly :
      ((finSuccFractionFieldMap n).comp
          (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
            (R := PolyFieldBase n))).comp
          (algebraMap (PolyFieldBase n) (RationalField n)) =
        (rationalFieldMap n).comp
          (algebraMap (PolyFieldBase n) (RationalField n)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change finSuccFractionFieldMap n
          (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
            (algebraMap (PolyFieldBase n) (RationalField n) (MvPolynomial.C a))) =
        rationalFieldMap n
          (algebraMap (PolyFieldBase n) (RationalField n) (MvPolynomial.C a))
      rw [Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap_algebraMap,
        finSuccFractionFieldMap_algebraMap, rationalFieldMap_algebraMap]
      have hsource : (finSuccPolynomialEquiv n).symm
          (Polynomial.C (MvPolynomial.C a)) = polynomialRename n (MvPolynomial.C a) := by
        calc
          (finSuccPolynomialEquiv n).symm (Polynomial.C (MvPolynomial.C a)) =
              (finSuccPolynomialEquiv n).symm
                (algebraMap (ZMod 2) (Polynomial (PolyFieldBase n)) a) := by
                  simp [Polynomial.algebraMap_apply]
          _ = algebraMap (ZMod 2) (PolyFieldBase (n + 1)) a :=
                (finSuccPolynomialEquiv n).symm.commutes a
          _ = polynomialRename n (MvPolynomial.C a) := by
                simp [polynomialRename]
      exact congrArg (algebraMap (PolyFieldBase (n + 1))
        (RationalField (n + 1))) hsource
    · intro i
      change finSuccFractionFieldMap n
          (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
            (algebraMap (PolyFieldBase n) (RationalField n) (MvPolynomial.X i))) =
        rationalFieldMap n
          (algebraMap (PolyFieldBase n) (RationalField n) (MvPolynomial.X i))
      rw [Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap_algebraMap,
        finSuccFractionFieldMap_old]
      simpa [genericCoordinate] using
        (rationalFieldMap_genericCoordinate n i).symm
  exact congrArg (fun f => f p) hpoly
#print axioms finSuccFractionFieldMap_comp_coeffMap
#print axioms finSuccFractionFieldMap_algebraMap
#print axioms rationalFieldMap_algebraMap
#print axioms polynomialRename_injective
#print axioms finSuccPolynomialEquiv
#print axioms finSuccPolynomialEquiv_old
#print axioms finSuccPolynomialEquiv_new
#print axioms finSuccFractionFieldMap_injective
#print axioms finSuccFractionFieldMap_old
#print axioms finSuccFractionFieldMap_new
#print axioms rationalFieldMap_base
#print axioms genericCoordinates_linearIndependent
#print axioms genericReciprocalSum_map

end Carlet.CandidatePaper.Section32GenericCoordinateField



