import Carlet.CandidatePaper.Section31ReciprocalCommonDenominator
import Carlet.CandidatePaper.GradedQuotient
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Degree bookkeeping for the cleared homogeneous components. -/

noncomputable section
namespace Carlet.CandidatePaper.Section31ReciprocalKernelHomogeneous

open Carlet.CandidatePaper.Section31ReciprocalCommonDenominator
open Carlet.CandidatePaper.Section31ReciprocalPresentation
open Carlet.CandidatePaper.Section31SymmetricAlgebraBridge
open Carlet.CandidatePaper.ReciprocalCoordinates
open Carlet.CandidatePaper.Section32ReciprocalRingBridge
open scoped BigOperators

local instance reciprocalGradedAlgebra (n : ℕ) :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule (BinaryVector n) (ZMod 2)) :=
  MvPolynomial.gradedAlgebra

def clearedComponentTerm (n N : ℕ) (p : reciprocalPolynomial n) (d : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) :=
  commonDenominator n ^ (N - d) * denominatorScaledEvaluation n
    (MvPolynomial.homogeneousComponent d p)

def clearedComponentDegree (M N d : ℕ) : ℕ :=
  M * (N - d) + (M - 1) * d

theorem clearedComponentTerm_isHomogeneous (n N : ℕ)
    (p : reciprocalPolynomial n) (d : ℕ) :
    (clearedComponentTerm n N p d).IsHomogeneous
      (clearedComponentDegree (nonzeroVectors n).card N d) := by
  unfold clearedComponentTerm clearedComponentDegree
  exact (MvPolynomial.IsHomogeneous.pow (commonDenominator_isHomogeneous n) (N - d)).mul
    (denominatorScaledEvaluation_preservesHomogeneity n
      (MvPolynomial.homogeneousComponent_isHomogeneous d p))

theorem clearedComponentDegree_eq (M N d : ℕ) (hM : 0 < M) (hd : d ≤ N) :
    clearedComponentDegree M N d = M * N - d := by
  unfold clearedComponentDegree
  rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
  simp only [one_mul]
  exact Nat.sub_add_sub_cancel (Nat.mul_le_mul_left M hd)
    (Nat.le_mul_of_pos_left d hM)

theorem clearedComponentDegree_injective (M N : ℕ) (hM : 0 < M)
    {d e : ℕ} (hd : d ≤ N) (he : e ≤ N)
    (h : clearedComponentDegree M N d = clearedComponentDegree M N e) : d = e := by
  rw [clearedComponentDegree_eq M N d hM hd, clearedComponentDegree_eq M N e hM he] at h
  have hd' : d ≤ M * N := le_trans hd (Nat.le_mul_of_pos_left N hM)
  have he' : e ≤ M * N := le_trans he (Nat.le_mul_of_pos_left N hM)
  omega

theorem clearedComponentTerm_field_eq (n N : ℕ) (p : reciprocalPolynomial n)
    (d : ℕ) (hd : d ≤ N) :
    algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
        (clearedComponentTerm n N p d) =
      (commonDenominatorInField n) ^ N *
        genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p) := by
  rw [clearedComponentTerm, map_mul, map_pow]
  rw [denominatorScaledEvaluation_field_eq_of_isHomogeneous n
    (MvPolynomial.homogeneousComponent_isHomogeneous d p)]
  calc
    commonDenominatorInField n ^ (N - d) *
        (commonDenominatorInField n ^ d *
          genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p)) =
        (commonDenominatorInField n ^ (N - d) * commonDenominatorInField n ^ d) *
          genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p) := by ac_rfl
    _ = commonDenominatorInField n ^ ((N - d) + d) *
          genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p) := by
            rw [← pow_add]
    _ = commonDenominatorInField n ^ N *
          genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p) := by
            rw [Nat.sub_add_cancel hd]

theorem commonDenominatorInField_ne_zero (n : ℕ) :
    commonDenominatorInField n ≠ 0 := by
  intro h
  have hpoly : commonDenominator n = 0 := by
    have hmap :
        algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
          (commonDenominator n) =
        algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n) 0 := by
      simpa [commonDenominatorInField] using h
    exact (IsFractionRing.injective (MvPolynomial (Fin n) (ZMod 2))
      (RationalFunctionField n)) hmap
  exact commonDenominator_nonzero n hpoly

theorem nonzeroVectors_card_pos (n : ℕ) (hn : 0 < n) : 0 < (nonzeroVectors n).card := by
  apply Finset.card_pos.mpr
  let i : Fin n := ⟨0, hn⟩
  let v : BinaryVector n := fun j => if j = i then 1 else 0
  have hv : v ≠ 0 := by
    intro hz
    have hzv := congrFun hz i
    simp [v, i] at hzv
  have hvMem : v ∈ nonzeroVectors n := by
    simp [nonzeroVectors, hv]
  exact ⟨v, hvMem⟩

theorem symmetricFractionEquiv_reciprocalEvaluation_eq (n : ℕ) :
    (symmetricFractionEquiv n).toRingHom.comp (reciprocalEvaluation n).toRingHom =
      (genericReciprocalEvaluation n).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change symmetricFractionEquiv n
        (MvPolynomial.aeval (fun v : BinaryVector n =>
          if v = 0 then 0 else
            (algebraMap (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n)
              (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v))⁻¹)
          (MvPolynomial.C c)) =
      MvPolynomial.aeval (fun v : BinaryVector n =>
        if v = 0 then 0 else reciprocalCoordinate n v) (MvPolynomial.C c)
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    rw [symmetricFractionEquiv]
    calc
      (IsFractionRing.ringEquivOfRingEquiv (symmetricPolynomialEquiv n).toRingEquiv)
          (algebraMap (ZMod 2) (CandidateSymmetricFractionField n) c) =
        (IsFractionRing.ringEquivOfRingEquiv (symmetricPolynomialEquiv n).toRingEquiv)
          (algebraMap (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n)
            (algebraMap (ZMod 2) (CandidateSymmetricAlgebra n) c)) := by
              exact congrArg _ (IsScalarTower.algebraMap_apply (ZMod 2)
                (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n) c).symm
      _ = algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
          (symmetricPolynomialEquiv n
            (algebraMap (ZMod 2) (CandidateSymmetricAlgebra n) c)) :=
              IsFractionRing.ringEquivOfRingEquiv_algebraMap
                (symmetricPolynomialEquiv n).toRingEquiv _
      _ = algebraMap (ZMod 2) (RationalFunctionField n) c := by
              rw [AlgEquiv.commutes]
              exact IsScalarTower.algebraMap_apply (ZMod 2)
                (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n) c
  · intro v
    change symmetricFractionEquiv n (reciprocalEvaluation n (MvPolynomial.X v)) =
      genericReciprocalEvaluation n (MvPolynomial.X v)
    simp only [reciprocalEvaluation, genericReciprocalEvaluation, MvPolynomial.aeval_X]
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv, reciprocalCoordinate, symmetricFractionEquiv_ι]

theorem symmetricFractionEquiv_reciprocalEvaluation_apply (n : ℕ)
    (p : reciprocalPolynomial n) :
    symmetricFractionEquiv n (reciprocalEvaluation n p) =
      genericReciprocalEvaluation n p := by
  have h := congrArg (fun f : reciprocalPolynomial n →+* RationalFunctionField n => f p)
    (symmetricFractionEquiv_reciprocalEvaluation_eq n)
  exact h

theorem genericEvaluation_kernel_homogeneous (n : ℕ) (hn : 0 < n)
    {p : reciprocalPolynomial n}
    (hp : genericReciprocalEvaluation n p = 0) :
    ∀ d, genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p) = 0 := by
  classical
  let N := p.totalDegree
  let s := Finset.range (N + 1)
  let M := (nonzeroVectors n).card
  have hM : 0 < M := by
    dsimp [M]
    exact nonzeroVectors_card_pos n hn
  have hcomponents :
      (∑ d ∈ s, MvPolynomial.homogeneousComponent d p) = p := by
    simpa [s, N] using MvPolynomial.sum_homogeneousComponent p
  have hevalComponents :
      (∑ d ∈ s, genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p)) = 0 := by
    calc
      (∑ d ∈ s, genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p)) =
          genericReciprocalEvaluation n (∑ d ∈ s, MvPolynomial.homogeneousComponent d p) := by
            rw [← map_sum]
      _ = genericReciprocalEvaluation n p := by rw [hcomponents]
      _ = 0 := hp
  have hpolynomialSum :
      (∑ d ∈ s, clearedComponentTerm n N p d) = 0 := by
    apply (IsFractionRing.injective (MvPolynomial (Fin n) (ZMod 2))
      (RationalFunctionField n))
    have hmap :
        algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)
          (∑ d ∈ s, clearedComponentTerm n N p d) =
        (commonDenominatorInField n) ^ N *
          (∑ d ∈ s, genericReciprocalEvaluation n
            (MvPolynomial.homogeneousComponent d p)) := by
      rw [map_sum]
      calc
        (∑ d ∈ s, algebraMap (MvPolynomial (Fin n) (ZMod 2))
            (RationalFunctionField n) (clearedComponentTerm n N p d)) =
          (∑ d ∈ s, (commonDenominatorInField n) ^ N *
            genericReciprocalEvaluation n (MvPolynomial.homogeneousComponent d p)) := by
              apply Finset.sum_congr rfl
              intro d hd
              have hdN : d ≤ N := by
                simp only [s, Finset.mem_range] at hd
                omega
              exact clearedComponentTerm_field_eq n N p d hdN
        _ = (commonDenominatorInField n) ^ N *
            (∑ d ∈ s, genericReciprocalEvaluation n
              (MvPolynomial.homogeneousComponent d p)) := by
                rw [← Finset.mul_sum]
    rw [hmap, hevalComponents]
    simp
  have htermZero := homogeneous_sum_eq_zero_each s
      (fun d => clearedComponentTerm n N p d)
      (fun d => clearedComponentDegree M N d)
      (by
        intro d hd
        exact clearedComponentTerm_isHomogeneous n N p d)
      (by
        intro d hd e he hde
        have hdN : d ≤ N := by
          simp only [s, Finset.mem_range] at hd
          omega
        have heN : e ≤ N := by
          simp only [s, Finset.mem_range] at he
          omega
        exact clearedComponentDegree_injective M N hM hdN heN hde)
      hpolynomialSum
  intro d
  by_cases hd : d ∈ s
  · have hz := htermZero d hd
    have hfield := congrArg
      (algebraMap (MvPolynomial (Fin n) (ZMod 2)) (RationalFunctionField n)) hz
    rw [map_zero, clearedComponentTerm_field_eq n N p d (by
      simp only [s, Finset.mem_range] at hd
      omega)] at hfield
    have hpow : (commonDenominatorInField n) ^ N ≠ 0 :=
      pow_ne_zero _ (commonDenominatorInField_ne_zero n)
    exact (mul_eq_zero.mp hfield).resolve_left hpow
  · have hlt : p.totalDegree < d := by
      have hnotlt : ¬ d < N + 1 := by
        simpa [s] using hd
      omega
    rw [MvPolynomial.homogeneousComponent_eq_zero d p hlt]
    simp

theorem reciprocalEvaluation_kernel_homogeneous (n : ℕ) (hn : 0 < n)
    {p : reciprocalPolynomial n}
    (hp : reciprocalEvaluation n p = 0) :
    ∀ d, reciprocalEvaluation n (MvPolynomial.homogeneousComponent d p) = 0 := by
  have hgeneric : genericReciprocalEvaluation n p = 0 := by
    calc
      genericReciprocalEvaluation n p =
          symmetricFractionEquiv n (reciprocalEvaluation n p) :=
            (symmetricFractionEquiv_reciprocalEvaluation_apply n p).symm
      _ = 0 := by rw [hp, map_zero]
  intro d
  have hcomponent := genericEvaluation_kernel_homogeneous n hn hgeneric d
  apply (symmetricFractionEquiv n).injective
  rw [symmetricFractionEquiv_reciprocalEvaluation_apply, map_zero]
  exact hcomponent

/-- The reciprocal evaluation kernel is homogeneous for the standard grading. -/
theorem reciprocalEvaluation_ker_isHomogeneous (n : ℕ) (hn : 0 < n) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (BinaryVector n) (ZMod 2))
      (RingHom.ker (reciprocalEvaluation n).toRingHom) := by
  intro d p hp
  simp only [DirectSum.decompose, Equiv.coe_fn_mk,
    MvPolynomial.decomposition.decompose'_apply]
  exact RingHom.mem_ker.mpr
    (reciprocalEvaluation_kernel_homogeneous n hn (RingHom.mem_ker.mp hp) d)

/-- The reciprocal evaluation kernel packaged as a Mathlib homogeneous ideal. -/
noncomputable def reciprocalEvaluationKernelIdeal (n : ℕ) (hn : 0 < n) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (BinaryVector n) (ZMod 2)) :=
  ⟨RingHom.ker (reciprocalEvaluation n).toRingHom,
    reciprocalEvaluation_ker_isHomogeneous n hn⟩

@[simp] theorem reciprocalEvaluationKernelIdeal_toIdeal (n : ℕ) (hn : 0 < n) :
    (reciprocalEvaluationKernelIdeal n hn).toIdeal =
      RingHom.ker (reciprocalEvaluation n).toRingHom := rfl

/-- The quotient grading induced by the homogeneous reciprocal-evaluation kernel. -/
noncomputable def reciprocalEvaluationQuotientGrading (n : ℕ) (hn : 0 < n) :
    ℕ → Submodule (ZMod 2)
      (reciprocalPolynomial n ⧸ (reciprocalEvaluationKernelIdeal n hn).toIdeal) :=
  HomogeneousIdeal.quotientGrading (reciprocalEvaluationKernelIdeal n hn)

@[instance_reducible] noncomputable def reciprocalEvaluationQuotientGradedAlgebra
    (n : ℕ) (hn : 0 < n) :
    GradedAlgebra (reciprocalEvaluationQuotientGrading n hn) := by
  unfold reciprocalEvaluationQuotientGrading
  infer_instance

theorem ellPolynomial_class_mem_degree_one (n : ℕ) (hn : 0 < n) :
    Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal (ellPolynomial n) ∈
      reciprocalEvaluationQuotientGrading n hn 1 := by
  unfold reciprocalEvaluationQuotientGrading
  apply HomogeneousIdeal.mk_mem_quotientGrading
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (ellPolynomial_homogeneous n)

theorem ellPolynomial_class_ne_zero (n : ℕ) (hn : 0 < n) :
    Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal (ellPolynomial n) ≠ 0 := by
  intro hzero
  have hmem : ellPolynomial n ∈ (reciprocalEvaluationKernelIdeal n hn).toIdeal :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  have heval : reciprocalEvaluation n (ellPolynomial n) = 0 := RingHom.mem_ker.mp hmem
  rw [ellPolynomial_maps_to_candidate] at heval
  exact candidatePaperEllInSymmetricFractionField_ne_zero n hn heval

/-- The reciprocal evaluation map with codomain restricted to the reciprocal
subalgebra generated in the manuscript's symmetric-algebra fraction field. -/
noncomputable def reciprocalEvaluationToSubring (n : ℕ) :
    reciprocalPolynomial n →ₐ[ZMod 2] candidateSymmetricReciprocalSubring n :=
  MvPolynomial.aeval (fun v : BinaryVector n =>
    if hv : v = 0 then 0 else
      ⟨(algebraMap (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n)
        (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v))⁻¹, by
          apply Algebra.subset_adjoin
          exact ⟨⟨v, hv⟩, rfl⟩⟩)

theorem reciprocalEvaluationToSubring_comp_val (n : ℕ) :
    (Subalgebra.val (candidateSymmetricReciprocalSubring n)).comp
        (reciprocalEvaluationToSubring n) = reciprocalEvaluation n := by
  classical
  apply MvPolynomial.algHom_ext
  intro v
  by_cases hv : v = 0
  · simp [reciprocalEvaluationToSubring, reciprocalEvaluation, hv]
  · simp [reciprocalEvaluationToSubring, reciprocalEvaluation, hv]

theorem reciprocalEvaluationToSubring_val (n : ℕ) (p : reciprocalPolynomial n) :
    (reciprocalEvaluationToSubring n p : CandidateSymmetricFractionField n) =
      reciprocalEvaluation n p := by
  exact congrArg (fun f : reciprocalPolynomial n →ₐ[ZMod 2]
    CandidateSymmetricFractionField n => f p) (reciprocalEvaluationToSubring_comp_val n)

theorem reciprocalEvaluationToSubring_surjective (n : ℕ) :
    Function.Surjective (reciprocalEvaluationToSubring n) := by
  classical
  intro x
  have hx : (x : CandidateSymmetricFractionField n) ∈
      Algebra.adjoin (ZMod 2) (candidateSymmetricReciprocalGenerators n) := x.property
  have hpreimage : ∃ p : reciprocalPolynomial n,
      reciprocalEvaluation n p = (x : CandidateSymmetricFractionField n) := by
    apply Algebra.adjoin_induction (R := ZMod 2) (A := CandidateSymmetricFractionField n)
      (s := candidateSymmetricReciprocalGenerators n)
      (p := fun y _ => ∃ p : reciprocalPolynomial n, reciprocalEvaluation n p = y)
    · intro y hy
      rcases hy with ⟨⟨v, hv⟩, rfl⟩
      exact ⟨MvPolynomial.X v, by simp [reciprocalEvaluation, hv]⟩
    · intro r
      exact ⟨MvPolynomial.C r, by simp [reciprocalEvaluation]⟩
    · intro a b ha hb hpa hpb
      rcases hpa with ⟨p, rfl⟩
      rcases hpb with ⟨q, rfl⟩
      exact ⟨p + q, by simp⟩
    · intro a b ha hb hpa hpb
      rcases hpa with ⟨p, rfl⟩
      rcases hpb with ⟨q, rfl⟩
      exact ⟨p * q, by simp⟩
    exact hx
  rcases hpreimage with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  rw [reciprocalEvaluationToSubring_val]
  exact hp

theorem reciprocalEvaluationToSubring_ker_eq (n : ℕ) :
    RingHom.ker (reciprocalEvaluationToSubring n).toRingHom =
      RingHom.ker (reciprocalEvaluation n).toRingHom := by
  ext p
  simp only [RingHom.mem_ker]
  change (reciprocalEvaluationToSubring n p = 0) ↔ reciprocalEvaluation n p = 0
  constructor
  · intro hp
    have hval := congrArg (fun z : candidateSymmetricReciprocalSubring n =>
      (z : CandidateSymmetricFractionField n)) hp
    simpa [reciprocalEvaluationToSubring_val] using hval
  · intro hp
    apply Subtype.ext
    rw [reciprocalEvaluationToSubring_val]
    exact hp

theorem reciprocalEvaluationToSubring_eq_zero_of_mem_kernel (n : ℕ) (hn : 0 < n)
    {p : reciprocalPolynomial n}
    (hp : p ∈ (reciprocalEvaluationKernelIdeal n hn).toIdeal) :
    reciprocalEvaluationToSubring n p = 0 := by
  have hker : p ∈ RingHom.ker (reciprocalEvaluationToSubring n).toRingHom := by
    rw [reciprocalEvaluationToSubring_ker_eq]
    exact hp
  exact RingHom.mem_ker.mp hker

/-- The homogeneous reciprocal quotient has the manuscript's reciprocal
subalgebra as its underlying ring. -/
noncomputable def reciprocalEvaluationQuotientRingEquiv (n : ℕ) (hn : 0 < n) :
    reciprocalPolynomial n ⧸ (reciprocalEvaluationKernelIdeal n hn).toIdeal ≃+*
      candidateSymmetricReciprocalSubring n := by
  have hker := reciprocalEvaluationToSubring_ker_eq n
  rw [reciprocalEvaluationKernelIdeal_toIdeal, ← hker]
  exact RingHom.quotientKerEquivOfSurjective
    (f := (reciprocalEvaluationToSubring n).toRingHom)
    (reciprocalEvaluationToSubring_surjective n)

noncomputable def reciprocalEvaluationQuotientAlgHom (n : ℕ) (hn : 0 < n) :
    reciprocalPolynomial n ⧸ (reciprocalEvaluationKernelIdeal n hn).toIdeal →ₐ[ZMod 2]
      candidateSymmetricReciprocalSubring n :=
  Ideal.Quotient.liftₐ (reciprocalEvaluationKernelIdeal n hn).toIdeal
    (reciprocalEvaluationToSubring n)
    (fun _p hp => reciprocalEvaluationToSubring_eq_zero_of_mem_kernel n hn hp)

@[simp] theorem reciprocalEvaluationQuotientAlgHom_mk (n : ℕ) (hn : 0 < n)
    (p : reciprocalPolynomial n) :
    reciprocalEvaluationQuotientAlgHom n hn
      (Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal p) =
        reciprocalEvaluationToSubring n p := by
  change (Ideal.Quotient.lift (reciprocalEvaluationKernelIdeal n hn).toIdeal
    (reciprocalEvaluationToSubring n).toRingHom
    (fun p hp => (reciprocalEvaluationToSubring_eq_zero_of_mem_kernel n hn hp :
      (reciprocalEvaluationToSubring n).toRingHom p = 0)))
      (Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal p) = _
  rw [Ideal.Quotient.lift_mk]
  rfl

theorem reciprocalEvaluationQuotientAlgHom_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (reciprocalEvaluationQuotientAlgHom n hn) := by
  intro x
  obtain ⟨p, hp⟩ := reciprocalEvaluationToSubring_surjective n x
  refine ⟨Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal p, ?_⟩
  rw [reciprocalEvaluationQuotientAlgHom_mk]
  exact hp

theorem reciprocalEvaluationQuotientAlgHom_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (reciprocalEvaluationQuotientAlgHom n hn) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [reciprocalEvaluationQuotientAlgHom_mk,
    reciprocalEvaluationQuotientAlgHom_mk] at hxy
  have heval : reciprocalEvaluation n p = reciprocalEvaluation n q := by
    have hval := congrArg (fun z : candidateSymmetricReciprocalSubring n =>
      (z : CandidateSymmetricFractionField n)) hxy
    simpa [reciprocalEvaluationToSubring_val] using hval
  apply (Ideal.Quotient.eq).2
  rw [reciprocalEvaluationKernelIdeal_toIdeal, RingHom.mem_ker]
  simp [map_sub, heval]

noncomputable def reciprocalEvaluationQuotientAlgEquiv (n : ℕ) (hn : 0 < n) :
    (reciprocalPolynomial n ⧸ (reciprocalEvaluationKernelIdeal n hn).toIdeal) ≃ₐ[ZMod 2]
      candidateSymmetricReciprocalSubring n :=
  AlgEquiv.ofBijective (reciprocalEvaluationQuotientAlgHom n hn)
    ⟨reciprocalEvaluationQuotientAlgHom_injective n hn,
      reciprocalEvaluationQuotientAlgHom_surjective n hn⟩

@[simp] theorem reciprocalEvaluationQuotientAlgEquiv_mk (n : ℕ) (hn : 0 < n)
    (p : reciprocalPolynomial n) :
    reciprocalEvaluationQuotientAlgEquiv n hn
      (Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal p) =
        reciprocalEvaluationToSubring n p := by
  change reciprocalEvaluationQuotientAlgHom n hn
    (Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal p) = _
  exact reciprocalEvaluationQuotientAlgHom_mk n hn p

theorem reciprocalEvaluationQuotientAlgEquiv_ellPolynomial (n : ℕ) (hn : 0 < n) :
    reciprocalEvaluationQuotientAlgEquiv n hn
      (Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal (ellPolynomial n)) =
        candidatePaperEllInSymmetricReciprocalSubring n := by
  apply Subtype.ext
  rw [reciprocalEvaluationQuotientAlgEquiv_mk,
    reciprocalEvaluationToSubring_val, ellPolynomial_maps_to_candidate]
  rfl

/-- The homogeneous pieces of the manuscript's reciprocal subalgebra, obtained
by transporting the quotient grading along its exact algebra equivalence. -/
abbrev reciprocalEvaluationSubringGrading (n : ℕ) (hn : 0 < n) (d : ℕ) :
    Submodule (ZMod 2) (candidateSymmetricReciprocalSubring n) :=
  Submodule.map (reciprocalEvaluationQuotientAlgEquiv n hn).toLinearEquiv.toLinearMap
    (reciprocalEvaluationQuotientGrading n hn d)

def reciprocalEvaluationSubringGradeEquiv (n : ℕ) (hn : 0 < n) (d : ℕ) :=
  (reciprocalEvaluationQuotientAlgEquiv n hn).toLinearEquiv.submoduleMap
    (reciprocalEvaluationQuotientGrading n hn d)

def reciprocalEvaluationSubringComponentSumMap (n : ℕ) (hn : 0 < n) :
    (DirectSum ℕ fun d => ↥(reciprocalEvaluationQuotientGrading n hn d)) →+
      DirectSum ℕ fun d => ↥(reciprocalEvaluationSubringGrading n hn d) :=
  DirectSum.map (fun d =>
    (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom)

set_option maxHeartbeats 1000000 in
def reciprocalEvaluationSubringComponentSumEquiv (n : ℕ) (hn : 0 < n) :
    (DirectSum ℕ fun d => ↥(reciprocalEvaluationQuotientGrading n hn d)) ≃+
      DirectSum ℕ fun d => ↥(reciprocalEvaluationSubringGrading n hn d) where
  toFun := reciprocalEvaluationSubringComponentSumMap n hn
  invFun := DirectSum.map (fun d =>
    (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom)
  left_inv := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [reciprocalEvaluationSubringComponentSumMap, map_zero]
    | of d z =>
        simp only [reciprocalEvaluationSubringComponentSumMap, DirectSum.map_of]
        congr 1
        exact (reciprocalEvaluationSubringGradeEquiv n hn d).symm_apply_apply z
    | add x y hx hy =>
        have hx' :
            (DirectSum.map (fun d =>
              (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom))
              ((DirectSum.map (fun d =>
                (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom)) x) = x := hx
        have hy' :
            (DirectSum.map (fun d =>
              (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom))
              ((DirectSum.map (fun d =>
                (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom)) y) = y := hy
        change (DirectSum.map (fun d =>
            (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom))
          ((DirectSum.map (fun d =>
            (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom) (x + y))) = x + y
        rw [(DirectSum.map (fun d =>
          (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom)).map_add,
          map_add, hx', hy']
  right_inv := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [reciprocalEvaluationSubringComponentSumMap, map_zero]
    | of d z =>
        simp only [reciprocalEvaluationSubringComponentSumMap, DirectSum.map_of]
        congr 1
        exact (reciprocalEvaluationSubringGradeEquiv n hn d).apply_symm_apply z
    | add x y hx hy =>
        have hx' :
            (DirectSum.map (fun d =>
              (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom))
              ((DirectSum.map (fun d =>
                (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom)) x) = x := hx
        have hy' :
            (DirectSum.map (fun d =>
              (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom))
              ((DirectSum.map (fun d =>
                (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom)) y) = y := hy
        change (DirectSum.map (fun d =>
            (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom))
          ((DirectSum.map (fun d =>
            (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom) (x + y))) = x + y
        rw [(DirectSum.map (fun d =>
          (reciprocalEvaluationSubringGradeEquiv n hn d).symm.toAddMonoidHom)).map_add,
          map_add, hx', hy']
  map_add' := (reciprocalEvaluationSubringComponentSumMap n hn).map_add

set_option maxHeartbeats 1000000 in
theorem reciprocalEvaluationSubringComponentSumMap_coe (n : ℕ) (hn : 0 < n)
    (x : DirectSum ℕ fun d => ↥(reciprocalEvaluationQuotientGrading n hn d)) :
    DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)
        (reciprocalEvaluationSubringComponentSumMap n hn x) =
      reciprocalEvaluationQuotientAlgEquiv n hn
        (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [reciprocalEvaluationSubringComponentSumMap, map_zero]
  | of d z =>
      rw [reciprocalEvaluationSubringComponentSumMap, DirectSum.map_of,
        DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
      exact LinearEquiv.submoduleMap_apply _ _ _
  | add x y hx hy =>
      calc
        _ = DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)
              (reciprocalEvaluationSubringComponentSumMap n hn x +
                reciprocalEvaluationSubringComponentSumMap n hn y) := by
                rw [(reciprocalEvaluationSubringComponentSumMap n hn).map_add]
        _ = DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)
                (reciprocalEvaluationSubringComponentSumMap n hn x) +
              DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)
                (reciprocalEvaluationSubringComponentSumMap n hn y) :=
                (DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)).map_add _ _
        _ = reciprocalEvaluationQuotientAlgEquiv n hn
                (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn) x) +
              reciprocalEvaluationQuotientAlgEquiv n hn
                (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn) y) := by
                rw [hx, hy]
        _ = reciprocalEvaluationQuotientAlgEquiv n hn
              (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn) x +
                DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn) y) :=
                ((reciprocalEvaluationQuotientAlgEquiv n hn).map_add _ _).symm
        _ = reciprocalEvaluationQuotientAlgEquiv n hn
              (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn) (x + y)) := by
                rw [(DirectSum.coeAddMonoidHom
                  (reciprocalEvaluationQuotientGrading n hn)).map_add]

/-! A componentwise direct-sum map acts on each homogeneous coefficient by its
corresponding component map. -/
theorem reciprocalEvaluationSubringComponentSumMap_component (n : ℕ) (hn : 0 < n)
    (x : DirectSum ℕ fun d => ↥(reciprocalEvaluationQuotientGrading n hn d)) (i : ℕ) :
    DirectSum.component (ZMod 2) ℕ
        (fun d => ↥(reciprocalEvaluationSubringGrading n hn d)) i
        (reciprocalEvaluationSubringComponentSumMap n hn x) =
      reciprocalEvaluationSubringGradeEquiv n hn i
        (DirectSum.component (ZMod 2) ℕ
          (fun d => ↥(reciprocalEvaluationQuotientGrading n hn d)) i x) := by
  change (DFinsupp.lapply i)
      (DFinsupp.mapRange
        (fun d => (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom)
        (by intro d; exact (reciprocalEvaluationSubringGradeEquiv n hn d).toAddMonoidHom.map_zero)
        x) = _
  rw [DFinsupp.lapply_apply, DFinsupp.mapRange_apply]
  rfl

noncomputable def reciprocalEvaluationQuotientDecompEquiv (n : ℕ) (hn : 0 < n) :
    (reciprocalPolynomial n ⧸ (reciprocalEvaluationKernelIdeal n hn).toIdeal) ≃
      DirectSum ℕ fun d => ↥(reciprocalEvaluationQuotientGrading n hn d) := by
  letI := reciprocalEvaluationQuotientGradedAlgebra n hn
  exact DirectSum.decompose (reciprocalEvaluationQuotientGrading n hn)

theorem reciprocalEvaluationQuotientDecompEquiv_coe (n : ℕ) (hn : 0 < n)
    (x : reciprocalPolynomial n ⧸ (reciprocalEvaluationKernelIdeal n hn).toIdeal) :
    DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn)
        (reciprocalEvaluationQuotientDecompEquiv n hn x) = x := by
  change (reciprocalEvaluationQuotientDecompEquiv n hn).symm
      (reciprocalEvaluationQuotientDecompEquiv n hn x) = x
  exact (reciprocalEvaluationQuotientDecompEquiv n hn).left_inv x

instance reciprocalEvaluationSubringGrading_one (n : ℕ) (hn : 0 < n) :
    SetLike.GradedOne (reciprocalEvaluationSubringGrading n hn) where
  one_mem := by
    rw [Submodule.mem_map]
    refine ⟨1, (reciprocalEvaluationQuotientGradedAlgebra n hn).one_mem, ?_⟩
    change (reciprocalEvaluationQuotientAlgEquiv n hn) 1 = 1
    exact map_one _

instance reciprocalEvaluationSubringGrading_mul (n : ℕ) (hn : 0 < n) :
    SetLike.GradedMul (reciprocalEvaluationSubringGrading n hn) where
  mul_mem := by
    intro i j x y hx hy
    rw [Submodule.mem_map] at hx hy ⊢
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    refine ⟨x' * y', (reciprocalEvaluationQuotientGradedAlgebra n hn).mul_mem hx' hy', ?_⟩
    change (reciprocalEvaluationQuotientAlgEquiv n hn) (x' * y') = _
    exact map_mul _ _ _

set_option maxHeartbeats 1000000 in
instance reciprocalEvaluationSubringGrading_decomposition (n : ℕ) (hn : 0 < n) :
    DirectSum.Decomposition (reciprocalEvaluationSubringGrading n hn) where
  decompose' x := reciprocalEvaluationSubringComponentSumEquiv n hn
    (reciprocalEvaluationQuotientDecompEquiv n hn
      ((reciprocalEvaluationQuotientAlgEquiv n hn).symm x))
  left_inv := by
    intro x
    change DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)
      (reciprocalEvaluationSubringComponentSumEquiv n hn
        (reciprocalEvaluationQuotientDecompEquiv n hn
          ((reciprocalEvaluationQuotientAlgEquiv n hn).symm x))) = x
    calc
      _ = reciprocalEvaluationQuotientAlgEquiv n hn
            (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn)
              (reciprocalEvaluationQuotientDecompEquiv n hn
                ((reciprocalEvaluationQuotientAlgEquiv n hn).symm x))) :=
              reciprocalEvaluationSubringComponentSumMap_coe n hn _
      _ = reciprocalEvaluationQuotientAlgEquiv n hn
            ((reciprocalEvaluationQuotientAlgEquiv n hn).symm x) := by
              rw [reciprocalEvaluationQuotientDecompEquiv_coe]
      _ = x := (reciprocalEvaluationQuotientAlgEquiv n hn).apply_symm_apply x
  right_inv := by
    intro x
    change reciprocalEvaluationSubringComponentSumEquiv n hn
      (reciprocalEvaluationQuotientDecompEquiv n hn
        ((reciprocalEvaluationQuotientAlgEquiv n hn).symm
          (DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn) x))) = x
    rw [← (reciprocalEvaluationSubringComponentSumEquiv n hn).apply_symm_apply x]
    apply congrArg (reciprocalEvaluationSubringComponentSumEquiv n hn)
    have h := reciprocalEvaluationSubringComponentSumMap_coe n hn
      ((reciprocalEvaluationSubringComponentSumEquiv n hn).symm x)
    change DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn)
      (reciprocalEvaluationSubringComponentSumEquiv n hn
        ((reciprocalEvaluationSubringComponentSumEquiv n hn).symm x)) = _ at h
    rw [(reciprocalEvaluationSubringComponentSumEquiv n hn).apply_symm_apply] at h
    rw [(reciprocalEvaluationSubringComponentSumEquiv n hn).apply_symm_apply]
    have hpre : (reciprocalEvaluationQuotientAlgEquiv n hn).symm
        (DirectSum.coeAddMonoidHom (reciprocalEvaluationSubringGrading n hn) x) =
          DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn)
            ((reciprocalEvaluationSubringComponentSumEquiv n hn).symm x) := by
      calc
        _ = (reciprocalEvaluationQuotientAlgEquiv n hn).symm
              ((reciprocalEvaluationQuotientAlgEquiv n hn)
                (DirectSum.coeAddMonoidHom (reciprocalEvaluationQuotientGrading n hn)
                  ((reciprocalEvaluationSubringComponentSumEquiv n hn).symm x))) := by rw [h]
        _ = _ := (reciprocalEvaluationQuotientAlgEquiv n hn).symm_apply_apply _
    rw [hpre]
    change reciprocalEvaluationQuotientDecompEquiv n hn
      ((reciprocalEvaluationQuotientDecompEquiv n hn).symm
        ((reciprocalEvaluationSubringComponentSumEquiv n hn).symm x)) = _
    exact (reciprocalEvaluationQuotientDecompEquiv n hn).right_inv _

set_option linter.style.haveILetI false in
instance reciprocalEvaluationSubringGradedAlgebra (n : ℕ) (hn : 0 < n) :
    GradedAlgebra (reciprocalEvaluationSubringGrading n hn) := by
  letI : SetLike.GradedMonoid (reciprocalEvaluationSubringGrading n hn) := by
    letI := reciprocalEvaluationSubringGrading_one n hn
    letI := reciprocalEvaluationSubringGrading_mul n hn
    exact SetLike.GradedMonoid.mk
  letI := reciprocalEvaluationSubringGrading_decomposition n hn
  exact GradedRing.mk

def reciprocalEvaluationQuotientGradedRingHom (n : ℕ) (hn : 0 < n) :
    reciprocalEvaluationQuotientGrading n hn →+*ᵍ reciprocalEvaluationSubringGrading n hn where
  toRingHom := (reciprocalEvaluationQuotientAlgEquiv n hn).toRingHom
  map_mem {d x} hx := by
    rw [reciprocalEvaluationSubringGrading, Submodule.mem_map]
    exact ⟨x, hx, rfl⟩

def reciprocalEvaluationSubringGradedRingHom (n : ℕ) (hn : 0 < n) :
    reciprocalEvaluationSubringGrading n hn →+*ᵍ reciprocalEvaluationQuotientGrading n hn where
  toRingHom := (reciprocalEvaluationQuotientAlgEquiv n hn).symm.toRingHom
  map_mem {d x} hx := by
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
    have hpre : (reciprocalEvaluationQuotientAlgEquiv n hn).symm x = y := by
      calc
        _ = (reciprocalEvaluationQuotientAlgEquiv n hn).symm
              ((reciprocalEvaluationQuotientAlgEquiv n hn) y) :=
                congrArg (reciprocalEvaluationQuotientAlgEquiv n hn).symm hxy.symm
        _ = _ := (reciprocalEvaluationQuotientAlgEquiv n hn).symm_apply_apply y
    change (reciprocalEvaluationQuotientAlgEquiv n hn).symm x ∈
      reciprocalEvaluationQuotientGrading n hn d
    rw [hpre]
    exact hy

theorem ellPolynomial_reciprocalSubring_mem_degree_one (n : ℕ) (hn : 0 < n) :
    reciprocalEvaluationToSubring n (ellPolynomial n) ∈
      reciprocalEvaluationSubringGrading n hn 1 := by
  rw [Submodule.mem_map]
  refine ⟨Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal
      (ellPolynomial n), ellPolynomial_class_mem_degree_one n hn, ?_⟩
  change reciprocalEvaluationQuotientAlgEquiv n hn
    (Ideal.Quotient.mk (reciprocalEvaluationKernelIdeal n hn).toIdeal (ellPolynomial n)) = _
  rw [reciprocalEvaluationQuotientAlgEquiv_mk]
#print axioms clearedComponentTerm_isHomogeneous
#print axioms clearedComponentDegree_eq
#print axioms clearedComponentDegree_injective
#print axioms clearedComponentTerm_field_eq
#print axioms commonDenominatorInField_ne_zero
#print axioms nonzeroVectors_card_pos
#print axioms symmetricFractionEquiv_reciprocalEvaluation_eq
#print axioms symmetricFractionEquiv_reciprocalEvaluation_apply
#print axioms genericEvaluation_kernel_homogeneous
#print axioms reciprocalEvaluation_kernel_homogeneous
#print axioms reciprocalEvaluation_ker_isHomogeneous
#print axioms reciprocalEvaluationKernelIdeal
#print axioms reciprocalEvaluationQuotientGradedAlgebra
#print axioms ellPolynomial_class_mem_degree_one
#print axioms ellPolynomial_class_ne_zero
#print axioms reciprocalEvaluationToSubring
#print axioms reciprocalEvaluationToSubring_comp_val
#print axioms reciprocalEvaluationToSubring_surjective
#print axioms reciprocalEvaluationToSubring_ker_eq
#print axioms reciprocalEvaluationQuotientRingEquiv
#print axioms reciprocalEvaluationQuotientAlgHom
#print axioms reciprocalEvaluationQuotientAlgHom_surjective
#print axioms reciprocalEvaluationQuotientAlgHom_injective
#print axioms reciprocalEvaluationQuotientAlgEquiv
#print axioms reciprocalEvaluationQuotientAlgEquiv_mk
#print axioms reciprocalEvaluationQuotientAlgEquiv_ellPolynomial
#print axioms reciprocalEvaluationSubringComponentSumEquiv
#print axioms reciprocalEvaluationSubringComponentSumMap_coe
#print axioms reciprocalEvaluationSubringComponentSumMap_component
#print axioms reciprocalEvaluationSubringGradedAlgebra
#print axioms reciprocalEvaluationQuotientGradedRingHom
#print axioms reciprocalEvaluationSubringGradedRingHom
#print axioms ellPolynomial_reciprocalSubring_mem_degree_one

end Carlet.CandidatePaper.Section31ReciprocalKernelHomogeneous

