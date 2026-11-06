import Carlet.CandidatePaper.Section32GenericCoordinateField
import Carlet.CandidatePaper.Section32IntegralDomainFiber
import Carlet.CandidatePaper.Section32CoordinateSplit
import Carlet.CandidatePaper.Section32InfiniteFiber
open MvPolynomial
open scoped BigOperators
open Carlet.CandidatePaper.Section32GenericCoordinateField
open Carlet.CandidatePaper.Section32IntegralDomainFiber
open Carlet.CandidatePaper.Section32CoordinateSplit
noncomputable section
namespace Carlet.CandidatePaper.Section32GenericReciprocalInduction
local instance (n : ℕ) : Algebra (RationalField n) (RationalField (n+1)) :=
  (rationalFieldMap n).toAlgebra
theorem algebraMap_eq_rationalFieldMap_local (n : ℕ) :
    algebraMap (RationalField n) (RationalField (n+1)) = rationalFieldMap n := rfl
local instance (n : ℕ) : IsScalarTower (ZMod 2) (RationalField n)
    (RationalField (n+1)) where
  smul_assoc a b c := by
    simp only [Algebra.smul_def, algebraMap_eq_rationalFieldMap_local]
    rw [map_mul]
    have ha : rationalFieldMap n (algebraMap (ZMod 2) (RationalField n) a) =
        algebraMap (ZMod 2) (RationalField (n+1)) a := by
      have h := congrArg (fun f : ZMod 2 →+* RationalField (n+1) => f a)
        (rationalFieldMap_base n)
      simpa [RingHom.comp_apply] using h
    rw [ha]
    ring
def binaryLinearFormPoly (n : ℕ) (u : Fin n → ZMod 2) : PolyFieldBase n :=
  ∑ i, (algebraMap (ZMod 2) (PolyFieldBase n) (u i)) * MvPolynomial.X i

def binaryLinearFormPolyNext (n : ℕ) (u : Fin n → ZMod 2) : PolyFieldBase (n+1) :=
  ∑ i, (algebraMap (ZMod 2) (PolyFieldBase (n+1)) (u i)) * MvPolynomial.X i.castSucc

theorem polynomialRename_binaryLinearForm (n : ℕ) (u : Fin n → ZMod 2) :
    polynomialRename n (binaryLinearFormPoly n u) = binaryLinearFormPolyNext n u := by
  simp [binaryLinearFormPoly, binaryLinearFormPolyNext, polynomialRename, MvPolynomial.rename_X]

theorem binaryLinearFormPoly_map (n : ℕ) (u : Fin n → ZMod 2) :
    algebraMap (PolyFieldBase n) (RationalField n) (binaryLinearFormPoly n u) =
      Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm (genericCoordinate n) u := by
  unfold binaryLinearFormPoly
  simp only [map_sum, map_mul]
  unfold Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
  simp only [Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar : algebraMap (PolyFieldBase n) (RationalField n)
          (algebraMap (ZMod 2) (PolyFieldBase n) (u i)) =
        algebraMap (ZMod 2) (RationalField n) (u i) := by
    exact (IsScalarTower.algebraMap_apply (ZMod 2) (PolyFieldBase n)
      (RationalField n) (u i)).symm
  rw [hscalar]
  simp [genericCoordinate]

theorem binaryLinearFormPoly_injective (n : ℕ) :
    Function.Injective (binaryLinearFormPoly n) := by
  intro u v huv
  have hK : Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm (genericCoordinate n) u =
      Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm (genericCoordinate n) v := by
    have h := congrArg (algebraMap (PolyFieldBase n) (RationalField n)) huv
    simpa [binaryLinearFormPoly_map] using h
  exact Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm_injective
    (genericCoordinate n) (genericCoordinates_linearIndependent n) hK

theorem genericReciprocalSum_eq_polyFormSum (n : ℕ) :
    (∑ u : Fin n → ZMod 2,
      (algebraMap (PolyFieldBase n) (RationalField n) (binaryLinearFormPoly n u))⁻¹) =
      Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n) := by
  unfold Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum
  apply Finset.sum_congr rfl
  intro u hu
  rw [binaryLinearFormPoly_map]

theorem finSuccPolynomialEquiv_symm_C (n : ℕ) (p : PolyFieldBase n) :
    (finSuccPolynomialEquiv n).symm (Polynomial.C p) = polynomialRename n p := by
  have heq :
      ((finSuccPolynomialEquiv n).symm.toRingEquiv.toRingHom).comp Polynomial.C =
        polynomialRename n := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (finSuccPolynomialEquiv n).symm (Polynomial.C (MvPolynomial.C a)) =
        polynomialRename n (MvPolynomial.C a)
      have hconst : Polynomial.C (MvPolynomial.C a) =
          algebraMap (ZMod 2) (Polynomial (PolyFieldBase n)) a := by
        simp [Polynomial.algebraMap_apply]
      rw [hconst, (finSuccPolynomialEquiv n).symm.commutes]
      simp [polynomialRename]
    · intro i
      have h := congrArg (finSuccPolynomialEquiv n).symm (finSuccPolynomialEquiv_old n i)
      simpa [polynomialRename] using h.symm
  exact congrArg (fun f => f p) heq

theorem finSuccPolynomialEquiv_symm_X (n : ℕ) :
    (finSuccPolynomialEquiv n).symm Polynomial.X = MvPolynomial.X (Fin.last n) := by
  have h := congrArg (finSuccPolynomialEquiv n).symm (finSuccPolynomialEquiv_new n)
  simpa using h.symm

theorem finSuccPolynomialEquiv_symm_factor (n : ℕ) (p : PolyFieldBase n) :
    (finSuccPolynomialEquiv n).symm (Polynomial.X + Polynomial.C p) =
      MvPolynomial.X (Fin.last n) + polynomialRename n p := by
  rw [map_add, finSuccPolynomialEquiv_symm_X, finSuccPolynomialEquiv_symm_C]

def fiberSum (n : ℕ) : FractionRing (Polynomial (PolyFieldBase n)) :=
  ∑ a ∈ Finset.univ.image (binaryLinearFormPoly n),
    (algebraMap (Polynomial (PolyFieldBase n))
      (FractionRing (Polynomial (PolyFieldBase n))) (Polynomial.X + Polynomial.C a))⁻¹

theorem fiberSum_map (n : ℕ) :
    finSuccFractionFieldMap n (fiberSum n) =
      ∑ u : Fin n → ZMod 2,
        (genericCoordinate (n+1) (Fin.last n) +
          Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
            (fun i : Fin n => genericCoordinate (n+1) i.castSucc) u)⁻¹ := by
  classical
  unfold fiberSum
  rw [map_sum]
  have hinj : Set.InjOn (binaryLinearFormPoly n)
      (↑(Finset.univ : Finset (Fin n → ZMod 2))) := by
    intro a ha b hb hab
    exact binaryLinearFormPoly_injective n hab
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [map_inv₀]
  rw [finSuccFractionFieldMap_algebraMap, finSuccPolynomialEquiv_symm_factor,
    polynomialRename_binaryLinearForm]
  rw [map_add, genericCoordinate]
  rw [← polynomialRename_binaryLinearForm n u,
    ← rationalFieldMap_algebraMap n (binaryLinearFormPoly n u)]
  rw [binaryLinearFormPoly_map]
  apply congrArg Inv.inv
  congr 1
  calc
    rationalFieldMap n (Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
        (genericCoordinate n) u) =
      Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
        (fun i => rationalFieldMap n (genericCoordinate n i)) u := by
          exact (Carlet.CandidatePaper.Section32InfiniteFiber.binaryLinearForm_algebraMap
            (x := genericCoordinate n) u).symm
    _ = Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
        (fun i : Fin n => genericCoordinate (n+1) i.castSucc) u := by
          simp [Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm,
            rationalFieldMap_genericCoordinate]
theorem genericReciprocalSum_succ_split (n : ℕ) :
    Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate (n+1)) =
      rationalFieldMap n (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) +
        finSuccFractionFieldMap n (fiberSum n) := by
  let x : Fin n → RationalField (n+1) := fun i => genericCoordinate (n+1) i.castSucc
  let t : RationalField (n+1) := genericCoordinate (n+1) (Fin.last n)
  have hxy : Fin.lastCases t x = genericCoordinate (n+1) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [x, t, genericCoordinate]
  rw [← hxy, Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum_lastCases]
  rw [← genericReciprocalSum_map n, fiberSum_map]
theorem genericReciprocalSum_one_ne_zero :
    Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate 1) ≠ 0 := by
  classical
  unfold Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum
  let u0 : Fin 1 → ZMod 2 := fun _ => 0
  let u1 : Fin 1 → ZMod 2 := fun _ => 1
  have huniv : (Finset.univ : Finset (Fin 1 → ZMod 2)) = {u0, u1} := by
    decide
  rw [huniv]
  have hx : genericCoordinate 1 0 ≠ 0 := by
    intro hz
    change algebraMap (PolyFieldBase 1) (RationalField 1) (MvPolynomial.X (0 : Fin 1)) = 0 at hz
    have hmap : algebraMap (PolyFieldBase 1) (RationalField 1) (MvPolynomial.X (0 : Fin 1)) =
        algebraMap (PolyFieldBase 1) (RationalField 1) 0 := by rw [hz, map_zero]
    have hpoly : (MvPolynomial.X (0 : Fin 1) : PolyFieldBase 1) = 0 :=
      (IsFractionRing.injective (PolyFieldBase 1) (RationalField 1)) hmap
    exact MvPolynomial.X_ne_zero 0 hpoly
  simp [u0, u1, Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm,
    genericCoordinate]
theorem genericReciprocalSum_succ_ne_zero (n : ℕ)
    (hn : Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n) ≠ 0) :
    Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate (n+1)) ≠ 0 := by
  have hnon : Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
      (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) + fiberSum n ≠ 0 :=
    Carlet.CandidatePaper.Section32IntegralDomainFiber.fractionConstant_add_fiberSum_ne_zero
      (Finset.univ.image (binaryLinearFormPoly n))
      (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) hn
  have hinj : Function.Injective (finSuccFractionFieldMap n) :=
    finSuccFractionFieldMap_injective n
  have hmap : finSuccFractionFieldMap n
      (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
        (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) + fiberSum n) =
      Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate (n+1)) := by
    rw [map_add]
    calc
      finSuccFractionFieldMap n (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap
          (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n))) +
        finSuccFractionFieldMap n (fiberSum n) =
          ((finSuccFractionFieldMap n).comp
            (Carlet.CandidatePaper.Section32IntegralDomainFiber.coeffMap))
            (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) +
          finSuccFractionFieldMap n (fiberSum n) := by rfl
      _ = rationalFieldMap n
          (Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n)) +
          finSuccFractionFieldMap n (fiberSum n) := by
            rw [finSuccFractionFieldMap_comp_coeffMap]
      _ = Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate (n+1)) :=
            (genericReciprocalSum_succ_split n).symm
  intro hz
  apply hnon
  apply hinj
  rw [hmap, hz]
  simp

theorem genericReciprocalSum_nonzero_of_pos (n : ℕ) (hn : 0 < n) :
    Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum (genericCoordinate n) ≠ 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hzero : n = 0
      · subst n
        simpa using genericReciprocalSum_one_ne_zero
      · have hprev : 0 < n := by omega
        have hprevsum := ih hprev
        simpa [Nat.succ_eq_add_one] using
          genericReciprocalSum_succ_ne_zero n hprevsum

def candidatePaperEll (n : ℕ) : RationalField n :=
  ∑ v ∈ (Finset.univ : Finset (Fin n → ZMod 2)).erase 0,
    (Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
      (genericCoordinate n) v)⁻¹

theorem candidatePaperEll_nonzero (n : ℕ) (hn : 0 < n) :
    candidatePaperEll n ≠ 0 := by
  unfold candidatePaperEll
  rw [← Carlet.CandidatePaper.Section32CoordinateSplit.binaryReciprocalSum_eq_sum_nonzero]
  exact genericReciprocalSum_nonzero_of_pos n hn
/-- The graded reciprocal subring from the candidate manuscript, modeled as the
subalgebra generated by all reciprocals of nonzero binary linear forms. -/
def candidateReciprocalSubring (n : ℕ) : Subalgebra (ZMod 2) (RationalField n) :=
  Algebra.adjoin (ZMod 2)
    (Set.range (fun v : {u : Fin n → ZMod 2 // u ≠ 0} =>
      (Carlet.CandidatePaper.Section32CoordinateSplit.binaryLinearForm
        (genericCoordinate n) v.1)⁻¹))

theorem candidatePaperEll_mem_reciprocalSubring (n : ℕ) :
    candidatePaperEll n ∈ candidateReciprocalSubring n := by
  classical
  unfold candidatePaperEll candidateReciprocalSubring
  apply Subalgebra.sum_mem
  intro v hv
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  apply Algebra.subset_adjoin
  exact ⟨⟨v, hv0⟩, rfl⟩

/-- The manuscript's finite reciprocal sum as an element of its generated ring. -/
def candidatePaperEllElement (n : ℕ) : candidateReciprocalSubring n :=
  ⟨candidatePaperEll n, candidatePaperEll_mem_reciprocalSubring n⟩

theorem candidatePaperEllElement_ne_zero (n : ℕ) (hn : 0 < n) :
    candidatePaperEllElement n ≠ 0 := by
  intro hz
  apply candidatePaperEll_nonzero n hn
  exact congrArg Subtype.val hz

#print axioms candidatePaperEll_mem_reciprocalSubring
#print axioms candidatePaperEllElement_ne_zero
#print axioms polynomialRename_binaryLinearForm
#print axioms binaryLinearFormPoly_map
#print axioms binaryLinearFormPoly_injective
#print axioms fiberSum_map
#print axioms genericReciprocalSum_succ_split
#print axioms genericReciprocalSum_succ_ne_zero
#print axioms genericReciprocalSum_nonzero_of_pos
#print axioms candidatePaperEll_nonzero

end Carlet.CandidatePaper.Section32GenericReciprocalInduction













