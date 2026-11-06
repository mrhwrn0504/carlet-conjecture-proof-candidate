import Carlet.FiniteCoordinates
import Carlet.Statement
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite

set_option linter.style.haveILetI false

/-!
Elementary normalization lemmas needed for the finite-field point/subspace
correspondence in Section 3 of the supplied manuscript.
-/

noncomputable section

open scoped BigOperators

namespace Carlet.CandidatePaper.Section3

open Carlet.Quadratic

variable {K : Type*} [Field K]

/-- Read a recursive bit vector as its coefficient function in F₂^r. -/
def bitsCoeff : (r : ℕ) → Bits r → Fin r → ZMod 2
  | 0, _, i => Fin.elim0 i
  | r + 1, (b, last), i =>
      Fin.lastCases (if last then 1 else 0) (fun j => bitsCoeff r b j) i

@[simp] theorem bitsCoeff_castSucc (r : ℕ) (b : Bits r) (last : Bool)
    (i : Fin r) : bitsCoeff (r + 1) (b, last) i.castSucc = bitsCoeff r b i := by
  simp [bitsCoeff]

@[simp] theorem bitsCoeff_last (r : ℕ) (b : Bits r) (last : Bool) :
    bitsCoeff (r + 1) (b, last) (Fin.last r) = if last then 1 else 0 := by
  simp [bitsCoeff]

theorem bitsCoeff_injective (r : ℕ) : Function.Injective (bitsCoeff r) := by
  induction r with
  | zero =>
    intro b c _
    cases b
    cases c
    rfl
  | succ r ih =>
    intro b c h
    rcases b with ⟨b, last⟩
    rcases c with ⟨c, last'⟩
    have hpre : bitsCoeff r b = bitsCoeff r c := by
      funext i
      have hi := congrFun h i.castSucc
      simpa using hi
    have hlast := congrFun h (Fin.last r)
    have hbool : last = last' := by
      cases last <;> cases last' <;> simp_all
    subst last'
    congr 1
    exact ih hpre

theorem bitsCoeff_bijective (r : ℕ) : Function.Bijective (bitsCoeff r) := by
  have hbits : Fintype.card (Bits r) = 2 ^ r := by
    induction r with
    | zero =>
        change Fintype.card PUnit = 1
        simp
    | succ r ih =>
        change Fintype.card (Bits r × Bool) = 2 ^ r * 2
        rw [Fintype.card_prod, Fintype.card_bool, ih]
  have hfun : Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
    simp
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact bitsCoeff_injective r
  · exact hbits.trans hfun.symm

noncomputable def bitsCoeffEquiv (r : ℕ) : Bits r ≃ (Fin r → ZMod 2) :=
  Equiv.ofBijective (bitsCoeff r) (bitsCoeff_bijective r)

theorem bitsCoeff_zeroBits (r : ℕ) : bitsCoeff r (zeroBits r) = 0 := by
  funext i
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [zeroBits]
    · simpa [zeroBits] using ih j

theorem combination_scale (a : K) (x : ℕ → K) (r : ℕ) (b : Bits r) :
    combination (fun j => a * x j) r b = a * combination x r b := by
  induction r with
  | zero => simp [combination]
  | succ r ih =>
    rcases b with ⟨b, flag⟩
    cases flag <;> simp [combination, ih, mul_add]

theorem combination_eq_coeff_sum [Algebra (ZMod 2) K]
    (x : ℕ → K) (r : ℕ) (b : Bits r) :
    combination x r b = ∑ i : Fin r, bitsCoeff r b i • x i.val := by
  induction r with
  | zero => simp [combination]
  | succ r ih =>
    rcases b with ⟨b, last⟩
    change combination x r b + (if last then x r else 0) = _
    rw [Fin.sum_univ_castSucc]
    simp only [bitsCoeff_castSucc, bitsCoeff_last]
    rw [ih]
    cases last <;> simp

/-- The manuscript's reciprocal sum is exactly the sum over all F₂
coefficient vectors. This is the finite combinatorial half of the point to
subspace bridge; identifying its indexing set with the span is established
separately by linear independence. -/
theorem reciprocalSum_eq_coeff_vectors [Algebra (ZMod 2) K]
    (x : ℕ → K) (r : ℕ) :
    fullReciprocalSum x r =
      ∑ g : Fin r → ZMod 2,
        Ring.inverse (∑ i : Fin r, g i • x i.val) := by
  classical
  unfold fullReciprocalSum
  rw [← Equiv.sum_comp (bitsCoeffEquiv r)]
  apply Finset.sum_congr rfl
  intro b hb
  change Ring.inverse (combination x r b) =
    Ring.inverse (∑ i : Fin r, bitsCoeff r b i • x i.val)
  exact congrArg Ring.inverse (combination_eq_coeff_sum x r b)

theorem openPoint_coordinates_linearIndependent [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    LinearIndependent (ZMod 2) (fun i : Fin r => y.val i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨b, hb⟩ := (bitsCoeff_bijective r).2 g
  have hcomb : combination (extendVector y.val) r b = 0 := by
    rw [combination_eq_coeff_sum]
    calc
      (∑ j : Fin r, bitsCoeff r b j • extendVector y.val j.val) =
          ∑ j : Fin r, g j • y.val j := by
            rw [hb]
            apply Finset.sum_congr rfl
            intro j hj
            simp [extendVector_apply]
      _ = 0 := hg
  have hbit : b = zeroBits r := by
    by_contra hne
    have hu := y.property.2.1 b hne
    have hnezero : combination (extendVector y.val) r b ≠ 0 :=
      isUnit_iff_ne_zero.mp hu
    exact hnezero hcomb
  have hcoeff : bitsCoeff r b = 0 := by rw [hbit, bitsCoeff_zeroBits]
  have hgi : g i = 0 := by
    have := congrFun (hb.symm.trans hcoeff) i
    simpa using this
  exact hgi

def openPointSpan [Algebra (ZMod 2) K] (r : ℕ) (y : OpenCarletPoint K r) :
    Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) (Set.range (fun i : Fin r => y.val i))

/-- Coordinate functions of a finite basis are equivalent to the elements of
the space. This is the basis-coordinate interface for the converse direction
of the manuscript's point/subspace correspondence. -/
noncomputable def basisCoefficientsEquiv [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (E : Submodule (ZMod 2) K)
    (b : Module.Basis (Fin r) (ZMod 2) E) : (Fin r → ZMod 2) ≃ E :=
  (Finsupp.equivFunOnFinite (α := Fin r) (M := ZMod 2)).symm.trans b.repr.symm

theorem basisCoefficientsEquiv_apply [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (E : Submodule (ZMod 2) K)
    (b : Module.Basis (Fin r) (ZMod 2) E) (g : Fin r → ZMod 2) :
    (basisCoefficientsEquiv r E b g : K) =
      ∑ i : Fin r, g i • (b i : K) := by
  classical
  change ((b.repr.symm (Finsupp.equivFunOnFinite.symm g) : E) : K) = _
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype]
  · simp
  · intro i
    simp

theorem reciprocalSum_eq_basis_subtype_sum [Fintype K]
    [Algebra (ZMod 2) K] (r : ℕ) (E : Submodule (ZMod 2) K)
    [Fintype E] (b : Module.Basis (Fin r) (ZMod 2) E) :
    fullReciprocalSum (extendVector (fun i : Fin r => (b i : K))) r =
      ∑ e : E, Ring.inverse (e : K) := by
  classical
  rw [reciprocalSum_eq_coeff_vectors]
  rw [← Equiv.sum_comp (basisCoefficientsEquiv r E b)]
  apply Finset.sum_congr rfl
  intro g hg
  rw [basisCoefficientsEquiv_apply]
  simp [extendVector_apply]

theorem openPointSpan_finrank [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    Module.finrank (ZMod 2) (openPointSpan r y) = r := by
  unfold openPointSpan
  rw [finrank_span_eq_card (openPoint_coordinates_linearIndependent r y)]
  simp

/-- Linear map taking F₂ coefficients to the corresponding vector in the
ambient field. -/
def coefficientCombinationMap [Algebra (ZMod 2) K]
    (r : ℕ) (x : Fin r → K) : (Fin r → ZMod 2) →ₗ[ZMod 2] K where
  toFun g := ∑ i : Fin r, g i • x i
  map_add' g h := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a g := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_smul]

/-- The coefficient-combination map has image exactly the span generated by
the coordinates. -/
theorem coefficientCombinationMap_range [Algebra (ZMod 2) K]
    (r : ℕ) (x : Fin r → K) :
    (coefficientCombinationMap r x).range =
      Submodule.span (ZMod 2) (Set.range x) := by
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    change (∑ i : Fin r, g i • x i) ∈ _
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [coefficientCombinationMap]

theorem openPoint_coefficientMap_range [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    (coefficientCombinationMap r y.val).range = openPointSpan r y := by
  exact coefficientCombinationMap_range r y.val

theorem coefficientCombinationMap_injective [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    Function.Injective (coefficientCombinationMap r y.val) := by
  classical
  intro a b hab
  have hli := openPoint_coordinates_linearIndependent r y
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  have hzero : coefficientCombinationMap r y.val (a - b) = 0 := by
    rw [map_sub, hab]
    simp
  change (∑ j : Fin r, (a - b) j • y.val j) = 0 at hzero
  have hi := hli (a - b) hzero i
  exact sub_eq_zero.mp hi

/-- A normalized open point identifies F₂^r bijectively with the underlying
set of its coordinate span. -/
noncomputable def coefficientsEquivOpenPointSpan [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    (Fin r → ZMod 2) ≃ openPointSpan r y := by
  classical
  apply Equiv.ofBijective
    (fun g => ⟨coefficientCombinationMap r y.val g, by
      rw [← openPoint_coefficientMap_range]
      exact ⟨g, rfl⟩⟩)
  constructor
  · intro a b h
    apply coefficientCombinationMap_injective r y
    exact congrArg Subtype.val h
  · intro z
    have hz : (z : K) ∈ (coefficientCombinationMap r y.val).range := by
      rw [openPoint_coefficientMap_range]
      exact z.property
    rcases hz with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

noncomputable instance openPointSpanFintype [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) : Fintype (openPointSpan r y) :=
  Fintype.ofEquiv (Fin r → ZMod 2) (coefficientsEquivOpenPointSpan r y)

theorem reciprocalSum_eq_openPointSpan_sum [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    fullReciprocalSum (extendVector y.val) r =
      ∑ z : openPointSpan r y, Ring.inverse (z : K) := by
  classical
  rw [reciprocalSum_eq_coeff_vectors]
  rw [← Equiv.sum_comp (coefficientsEquivOpenPointSpan r y)]
  apply Finset.sum_congr rfl
  intro g hg
  simp [coefficientsEquivOpenPointSpan, coefficientCombinationMap,
    extendVector_apply]

theorem openPoint_sum_condition_iff_span_reciprocal_sum [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    fullReciprocalSum (extendVector y.val) r = 0 ↔
      (∑ z : openPointSpan r y, (z : K)⁻¹) = 0 := by
  rw [reciprocalSum_eq_openPointSpan_sum]
  simp only [Ring.inverse_eq_inv]

theorem isZeroSum_iff_subtype_reciprocal_sum [Fintype K] [Algebra (ZMod 2) K]
    (E : Submodule (ZMod 2) K) [Fintype E] :
    IsZeroSum E ↔ (∑ x : E, Ring.inverse (x : K)) = 0 := by
  classical
  have htotal : (∑ x : E, Ring.inverse (x : K)) =
      ∑ x ∈ underlyingFinset E, Ring.inverse x := by
    symm
    exact Finset.sum_subtype (underlyingFinset E)
      (by intro x; exact mem_underlyingFinset E x)
      (fun x => Ring.inverse x)
  have hzero : (0 : K) ∈ underlyingFinset E := by
    simp [mem_underlyingFinset]
  have hsplit := Finset.sum_erase_add (underlyingFinset E)
    (fun x : K => Ring.inverse x) hzero
  change (∑ x ∈ (underlyingFinset E).erase 0, x⁻¹) = 0 ↔ _
  have herase : (∑ x ∈ (underlyingFinset E).erase 0, x⁻¹) =
      ∑ x ∈ (underlyingFinset E).erase 0, Ring.inverse x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Ring.inverse_eq_inv x).symm
  have hsumEq : (∑ x ∈ (underlyingFinset E).erase 0, Ring.inverse x) =
      ∑ x : E, Ring.inverse (x : K) := by
    calc
      _ = _ + Ring.inverse (0 : K) := by simp
      _ = ∑ x ∈ underlyingFinset E, Ring.inverse x := hsplit
      _ = ∑ x : E, Ring.inverse (x : K) := htotal.symm
  rw [herase]
  rw [hsumEq]

/-- The manuscript's reciprocal-sum equation is basis-independent: for any
basis of a finite subspace, it vanishes exactly when the subspace is zero-sum. -/
theorem basis_reciprocal_sum_eq_zero_iff_isZeroSum [Fintype K]
    [Algebra (ZMod 2) K] (r : ℕ) (E : Submodule (ZMod 2) K)
    [Fintype E] (b : Module.Basis (Fin r) (ZMod 2) E) :
    fullReciprocalSum (extendVector (fun i : Fin r => (b i : K))) r = 0 ↔
      IsZeroSum E := by
  rw [reciprocalSum_eq_basis_subtype_sum]
  simpa only [Ring.inverse_eq_inv] using
    (isZeroSum_iff_subtype_reciprocal_sum E).symm

theorem basis_combination_ne_zero [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (E : Submodule (ZMod 2) K)
    (b : Module.Basis (Fin r) (ZMod 2) E) (bits : Bits r)
    (hbits : bits ≠ zeroBits r) :
    combination (extendVector (fun i : Fin r => (b i : K))) r bits ≠ 0 := by
  classical
  let g := bitsCoeff r bits
  have hg : g ≠ 0 := by
    intro hz
    apply hbits
    apply bitsCoeff_injective r
    calc
      bitsCoeff r bits = g := rfl
      _ = 0 := hz
      _ = bitsCoeff r (zeroBits r) := (bitsCoeff_zeroBits r).symm
  rw [combination_eq_coeff_sum]
  intro hsum
  have hlin := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hlin
  have hsub : (∑ i : Fin r, g i • b i) = 0 := by
    apply Subtype.ext
    simpa [g] using hsum
  have hcoeff := hlin g hsub
  apply hg
  funext i
  exact hcoeff i

theorem openPoint_condition_iff_zeroSumSpan [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) :
    fullReciprocalSum (extendVector y.val) r = 0 ↔
      IsZeroSum (openPointSpan r y) := by
  rw [openPoint_sum_condition_iff_span_reciprocal_sum]
  simpa only [Ring.inverse_eq_inv] using
    (isZeroSum_iff_subtype_reciprocal_sum (openPointSpan r y)).symm

theorem openPoint_yields_zeroSumSubspace [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (y : OpenCarletPoint K r) : HasZeroSumSubspace K r := by
  exact ⟨openPointSpan r y, openPointSpan_finrank r y,
    (openPoint_condition_iff_zeroSumSpan r y).mp y.property.2.2⟩

/-- Scaling every normalized coordinate by a nonzero field element scales
the full reciprocal sum by its inverse. The zero vector contributes zero on
both sides; all other denominators are assumed nonzero. -/
theorem fullReciprocalSum_scale (a : K) (ha : a ≠ 0) (x : ℕ → K) (r : ℕ)
    (hx : ∀ b : Bits r, b ≠ zeroBits r → combination x r b ≠ 0) :
    fullReciprocalSum (fun j => a * x j) r =
      Ring.inverse a * fullReciprocalSum x r := by
  classical
  have hau : IsUnit a := isUnit_iff_ne_zero.mpr ha
  unfold fullReciprocalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h0 : b = zeroBits r
  · subst b
    simp only [combination_zeroBits, Ring.inverse_zero, mul_zero]
  · rw [combination_scale]
    have hbu : IsUnit (combination x r b) := isUnit_iff_ne_zero.mpr (hx b h0)
    rw [Ring.inverse_mul (a := a) (b := combination x r b) (Or.inl hau)]
    ring

theorem fullReciprocalSum_scale_eq_zero_iff (a : K) (ha : a ≠ 0)
    (x : ℕ → K) (r : ℕ)
    (hx : ∀ b : Bits r, b ≠ zeroBits r → combination x r b ≠ 0) :
    fullReciprocalSum (fun j => a * x j) r = 0 ↔ fullReciprocalSum x r = 0 := by
  rw [fullReciprocalSum_scale a ha x r hx]
  have hInv : Ring.inverse a ≠ 0 := by
    intro hzero
    have hcancel := Ring.mul_inverse_cancel a (isUnit_iff_ne_zero.mpr ha)
    have hbad : (0 : K) = 1 := by
      simp only [hzero, mul_zero] at hcancel
      exact hcancel
    exact zero_ne_one hbad
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hInv
  · intro h
    rw [h, mul_zero]

/-- An arbitrary ordered basis of a zero-sum subspace gives a normalized open
point after scaling by the inverse of its first basis vector. -/
noncomputable def openPointOfZeroSumBasis [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (E : Submodule (ZMod 2) K) [Fintype E]
    (b : Module.Basis (Fin r) (ZMod 2) E) (hr : 0 < r)
    (hE : IsZeroSum E) : OpenCarletPoint K r := by
  classical
  let i₀ : Fin r := ⟨0, hr⟩
  let a : K := ((b i₀ : E) : K)⁻¹
  have hb0E : b i₀ ≠ 0 := b.linearIndependent.ne_zero i₀
  have hb0 : ((b i₀ : E) : K) ≠ 0 := by
    intro hz
    exact hb0E (Subtype.ext hz)
  have ha : a ≠ 0 := inv_ne_zero hb0
  let base : ℕ → K := extendVector (fun i : Fin r => (b i : K))
  let x : Fin r → K := fun i => a * (b i : K)
  have hcoord : extendVector x = fun j => a * base j := by
    funext j
    by_cases hj : j < r
    · simp [x, base, extendVector, hj]
    · simp [base, extendVector, hj]
  refine ⟨x, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [extendVector, x, a, i₀, hr, inv_mul_cancel₀ hb0]
  · intro bits hbits
    apply isUnit_iff_ne_zero.mpr
    rw [hcoord, combination_scale]
    exact mul_ne_zero ha (basis_combination_ne_zero r E b bits hbits)
  · have hbase :=
      (basis_reciprocal_sum_eq_zero_iff_isZeroSum r E b).mpr hE
    have hbaseRank : ∀ bits : Bits r, bits ≠ zeroBits r →
        combination base r bits ≠ 0 := by
      intro bits hbits
      exact basis_combination_ne_zero r E b bits hbits
    have hscale := fullReciprocalSum_scale a ha base r hbaseRank
    rw [hcoord, hscale, hbase]
    simp

/-- Every positive-dimensional zero-sum subspace determines a normalized
open point. The finite basis is reindexed using the exact finrank equality. -/
noncomputable def openPointOfZeroSumSubspace [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (E : Submodule (ZMod 2) K) [Fintype E]
    (hr : 0 < r) (hdim : Module.finrank (ZMod 2) E = r)
    (hE : IsZeroSum E) : OpenCarletPoint K r := by
  classical
  let I := Module.Basis.ofVectorSpaceIndex (ZMod 2) E
  letI : Fintype I := Fintype.ofFinite I
  let b0 := Module.Basis.ofVectorSpace (ZMod 2) E
  have hcard : Fintype.card I = r := by
    have hbcard := Module.finrank_eq_card_basis b0
    exact hbcard.symm.trans hdim
  let e : I ≃ Fin r := (Fintype.equivFin I).trans (Fin.castOrderIso hcard).toEquiv
  let b := b0.reindex e
  exact openPointOfZeroSumBasis r E b hr hE

/-- The affine finite-field point equation is exactly equivalent to the
existence of an r-dimensional zero-sum subspace, for every positive r. -/
theorem exists_openPoint_iff_hasZeroSumSubspace [Fintype K]
    [Algebra (ZMod 2) K] (r : ℕ) (hr : 0 < r) :
    (Nonempty (OpenCarletPoint K r)) ↔ HasZeroSumSubspace K r := by
  constructor
  · rintro ⟨y⟩
    exact openPoint_yields_zeroSumSubspace r y
  · rintro ⟨E, hdim, hE⟩
    classical
    letI : Fintype E := Fintype.ofFinite E
    exact ⟨openPointOfZeroSumSubspace r E hr hdim hE⟩

#print axioms combination_scale
#print axioms combination_eq_coeff_sum
#print axioms bitsCoeff_injective
#print axioms bitsCoeff_bijective
#print axioms bitsCoeffEquiv
#print axioms bitsCoeff_zeroBits
#print axioms reciprocalSum_eq_coeff_vectors
#print axioms openPoint_coordinates_linearIndependent
#print axioms openPointSpan_finrank
#print axioms coefficientCombinationMap_range
#print axioms openPoint_coefficientMap_range
#print axioms coefficientCombinationMap_injective
#print axioms coefficientsEquivOpenPointSpan
#print axioms reciprocalSum_eq_openPointSpan_sum
#print axioms openPoint_sum_condition_iff_span_reciprocal_sum
#print axioms isZeroSum_iff_subtype_reciprocal_sum
#print axioms openPoint_condition_iff_zeroSumSpan
#print axioms openPoint_yields_zeroSumSubspace
#print axioms fullReciprocalSum_scale
#print axioms fullReciprocalSum_scale_eq_zero_iff
#print axioms basisCoefficientsEquiv
#print axioms basisCoefficientsEquiv_apply
#print axioms reciprocalSum_eq_basis_subtype_sum
#print axioms basis_reciprocal_sum_eq_zero_iff_isZeroSum
#print axioms basis_combination_ne_zero
#print axioms openPointOfZeroSumBasis
#print axioms openPointOfZeroSumSubspace
#print axioms exists_openPoint_iff_hasZeroSumSubspace

end Carlet.CandidatePaper.Section3

