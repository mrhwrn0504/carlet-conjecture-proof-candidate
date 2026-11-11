import Carlet.CandidatePaper.Section32ReciprocalRingBridge
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
A homogeneous polynomial presentation of the manuscript's section. This is a
presentation map into the reciprocal subalgebra; proving that its kernel is
homogeneous is still required to transfer the grading to the image.
-/

noncomputable section
namespace Carlet.CandidatePaper.Section31ReciprocalPresentation

open Carlet.CandidatePaper.Section32ReciprocalRingBridge
open Carlet.CandidatePaper.Section31SymmetricAlgebraBridge
open scoped BigOperators

universe u v w

private theorem weightOne_eq_degree {σ : Type u} :
    Finsupp.weight (fun _ : σ => 1) = Finsupp.degree := by
  apply AddMonoidHom.ext
  intro d
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i a d hi ha ih =>
      rw [map_add, map_add, ih]
      simp [Finsupp.weight_single]

/-- A homogeneous polynomial has no component in any other degree. -/
theorem homogeneousComponent_eq_zero_of_isHomogeneous_of_ne
    {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R} {m n : ℕ}
    (hp : p.IsHomogeneous n) (hmn : m ≠ n) :
    MvPolynomial.homogeneousComponent m p = 0 := by
  rw [MvPolynomial.homogeneousComponent_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hmem : d ∈ p.support := (Finset.mem_filter.mp hd).1
  have hdeg : Finsupp.degree d = m := (Finset.mem_filter.mp hd).2
  have hcoeff : MvPolynomial.coeff d p ≠ 0 := by
    intro hz
    exact (MvPolynomial.mem_support_iff.mp hmem) hz
  have hdeg' := hp hcoeff
  change (Finsupp.weight (fun _ : σ => 1)) d = n at hdeg'
  have hweight : (Finsupp.weight (fun _ : σ => 1)) d = Finsupp.degree d :=
    congrArg (fun f => f d) weightOne_eq_degree
  rw [hweight] at hdeg'
  exact False.elim (hmn (hdeg.symm.trans hdeg'))

/-- Evaluating a homogeneous polynomial after multiplying each generator by a
common scalar multiplies its value by the corresponding scalar power. -/
theorem aeval_smul_of_isHomogeneous {R : Type v} {S : Type w} {σ : Type u}
    [CommSemiring R] [CommSemiring S] [Algebra R S] (c : S) (g : σ → S)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (fun i => c * g i) p = c ^ d * MvPolynomial.aeval g p := by
  classical
  have hsum : p = ∑ e ∈ p.support, (MvPolynomial.monomial e) (MvPolynomial.coeff e p) :=
    MvPolynomial.as_sum p
  have hmap : (MvPolynomial.aeval g) p =
      ∑ e ∈ p.support, (MvPolynomial.aeval g)
        ((MvPolynomial.monomial e) (MvPolynomial.coeff e p)) := by
    calc
      (MvPolynomial.aeval g) p =
          (MvPolynomial.aeval g)
            (∑ e ∈ p.support, (MvPolynomial.monomial e) (MvPolynomial.coeff e p)) := by
              conv_lhs => rw [hsum]
      _ = _ := by rw [map_sum]
  conv_lhs => rw [hsum]
  rw [map_sum]
  calc
    (∑ e ∈ p.support,
        (MvPolynomial.aeval fun i => c * g i) ((MvPolynomial.monomial e) (MvPolynomial.coeff e p))) =
      c ^ d * ∑ e ∈ p.support,
        (MvPolynomial.aeval g) ((MvPolynomial.monomial e) (MvPolynomial.coeff e p)) := by
          conv_rhs => rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          have heSupport : MvPolynomial.coeff e p ≠ 0 := by
            intro hz
            exact (MvPolynomial.mem_support_iff.mp he) hz
          have heDegreeW := hp heSupport
          have heDegree : Finsupp.degree e = d := by
            have hweight : (Finsupp.weight (fun _ : σ => 1)) e = Finsupp.degree e :=
              congrArg (fun f => f e) weightOne_eq_degree
            change (Finsupp.weight (fun _ : σ => 1)) e = d at heDegreeW
            rw [hweight] at heDegreeW
            exact heDegreeW
          rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
          have hprod : e.prod (fun i k => (c * g i) ^ k) =
              c ^ Finsupp.degree e * e.prod (fun i k => g i ^ k) := by
            calc
              e.prod (fun i k => (c * g i) ^ k) =
                  e.prod (fun i k => c ^ k * g i ^ k) := by
                    apply Finsupp.prod_congr
                    intro i hi
                    simp [mul_pow]
              _ = e.prod (fun i k => c ^ k) * e.prod (fun i k => g i ^ k) := by
                    rw [Finsupp.prod_mul]
              _ = c ^ Finsupp.degree e * e.prod (fun i k => g i ^ k) := by
                    congr 1
                    change (∏ i ∈ e.support, c ^ e i) = c ^ Finsupp.degree e
                    rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
          rw [hprod, heDegree]
          ring
    _ = c ^ d * (MvPolynomial.aeval g) p := by
          exact congrArg (fun z => c ^ d * z) hmap.symm

/-- A finite sum of homogeneous polynomials of pairwise distinct degrees can
vanish only when each summand vanishes. -/
theorem homogeneous_sum_eq_zero_each {ι : Type*} [DecidableEq ι]
    {σ R : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → MvPolynomial σ R) (degree : ι → ℕ)
    (hhom : ∀ i ∈ s, (f i).IsHomogeneous (degree i))
    (hinj : ∀ i ∈ s, ∀ j ∈ s, degree i = degree j → i = j)
    (hsum : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  intro i hi
  have hcomp := congrArg (MvPolynomial.homogeneousComponent (degree i)) hsum
  rw [map_sum] at hcomp
  have hcollapse :
      (∑ j ∈ s, MvPolynomial.homogeneousComponent (degree i) (f j)) = f i := by
    calc
      (∑ j ∈ s, MvPolynomial.homogeneousComponent (degree i) (f j)) =
          MvPolynomial.homogeneousComponent (degree i) (f i) := by
            refine Finset.sum_eq_single_of_mem (s := s)
              (f := fun j => MvPolynomial.homogeneousComponent (degree i) (f j)) i hi ?_
            intro j hj hji
            by_cases hdeg : degree i = degree j
            · exact False.elim (hji (hinj i hi j hj hdeg).symm)
            · exact homogeneousComponent_eq_zero_of_isHomogeneous_of_ne (hhom j hj) hdeg
      _ = f i := MvPolynomial.homogeneousComponent_eq_self (hhom i hi)
  rw [hcollapse] at hcomp
  simpa using hcomp

/-- Formal homogeneous coordinates indexed by all binary vectors. The zero
coordinate is sent to zero, so it contributes nothing to the section. -/
abbrev reciprocalPolynomial (n : ℕ) :=
  MvPolynomial (BinaryVector n) (ZMod 2)

def reciprocalEvaluation (n : ℕ) :
    reciprocalPolynomial n →ₐ[ZMod 2] CandidateSymmetricFractionField n :=
  MvPolynomial.aeval (fun v : BinaryVector n =>
    if v = 0 then 0 else
      (algebraMap (CandidateSymmetricAlgebra n) (CandidateSymmetricFractionField n)
        (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v))⁻¹)

def ellPolynomial (n : ℕ) : reciprocalPolynomial n :=
  ∑ v ∈ (Finset.univ : Finset (BinaryVector n)).erase 0, MvPolynomial.X v

theorem ellPolynomial_homogeneous (n : ℕ) : (ellPolynomial n).IsHomogeneous 1 := by
  classical
  unfold ellPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro v _
  exact MvPolynomial.isHomogeneous_X (ZMod 2) v

/-- The degree-one homogeneous component of the formal section is the section
itself. This is the component-level statement used when descending the
presentation to a graded quotient. -/
theorem ellPolynomial_component_one (n : ℕ) :
    MvPolynomial.homogeneousComponent 1 (ellPolynomial n) = ellPolynomial n :=
  MvPolynomial.homogeneousComponent_eq_self (ellPolynomial_homogeneous n)

theorem ellPolynomial_maps_to_candidate (n : ℕ) :
    reciprocalEvaluation n (ellPolynomial n) = candidatePaperEllInSymmetricFractionField n := by
  classical
  unfold reciprocalEvaluation ellPolynomial candidatePaperEllInSymmetricFractionField
  simp only [map_sum, MvPolynomial.aeval_X]
  apply Finset.sum_congr rfl
  intro v hv
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  simp [hv0]

#print axioms ellPolynomial_homogeneous
#print axioms ellPolynomial_component_one
#print axioms ellPolynomial_maps_to_candidate
#print axioms homogeneousComponent_eq_zero_of_isHomogeneous_of_ne
#print axioms aeval_smul_of_isHomogeneous
#print axioms homogeneous_sum_eq_zero_each

end Carlet.CandidatePaper.Section31ReciprocalPresentation
