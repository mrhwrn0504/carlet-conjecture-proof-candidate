import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace Carlet.CandidatePaper.Section32IntegralDomainFiber
open Polynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] [IsDomain R]

def rootProduct (s : Finset R) : R[X] := ∏ a ∈ s, (X + C a)

omit [IsDomain R] in
theorem rootProduct_monic (s : Finset R) : (rootProduct s).Monic := by
  classical
  exact Polynomial.monic_prod_of_monic s _ (fun a ha => monic_X_add_C a)

omit [IsDomain R] in
theorem fraction_map_poly_ne_zero {p : R[X]} (hp : p ≠ 0) :
    algebraMap R[X] (FractionRing R[X]) p ≠ 0 := by
  intro h
  apply hp
  exact (IsFractionRing.injective (R[X]) (FractionRing R[X])) (by simpa using h)

theorem sum_inverse_linearFactors_eq_logDerivative (s : Finset R) :
    (∑ a ∈ s, (algebraMap R[X] (FractionRing R[X]) (X + C a))⁻¹) =
      algebraMap R[X] (FractionRing R[X]) ((rootProduct s).derivative) *
        (algebraMap R[X] (FractionRing R[X]) (rootProduct s))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootProduct]
  | @insert a s ha ih =>
      have hprod : rootProduct (insert a s) = (X + C a) * rootProduct s := by
        simp [rootProduct, ha]
      have hderiv : (rootProduct (insert a s)).derivative =
          rootProduct s + (X + C a) * (rootProduct s).derivative := by
        rw [hprod, derivative_mul, derivative_X_add_C]
        simp
      let A : FractionRing R[X] := algebraMap R[X] (FractionRing R[X]) (X + C a)
      let B : FractionRing R[X] := algebraMap R[X] (FractionRing R[X]) (rootProduct s)
      let C' : FractionRing R[X] := algebraMap R[X] (FractionRing R[X]) ((rootProduct s).derivative)
      have hA : A ≠ 0 := by
        dsimp [A]
        exact fraction_map_poly_ne_zero (monic_X_add_C a).ne_zero
      have hB : B ≠ 0 := by
        dsimp [B]
        exact fraction_map_poly_ne_zero (rootProduct_monic s).ne_zero
      have hderiv_map : algebraMap R[X] (FractionRing R[X])
          ((rootProduct (insert a s)).derivative) = B + A * C' := by
        rw [hderiv, map_add, map_mul]
      have hprod_map : algebraMap R[X] (FractionRing R[X])
          (rootProduct (insert a s)) = A * B := by
        rw [hprod, map_mul]
      rw [Finset.sum_insert ha, hderiv_map, hprod_map, ih]
      change A⁻¹ + C' * B⁻¹ = (B + A * C') * (A * B)⁻¹
      field_simp [hA, hB]

noncomputable def coeffMap : FractionRing R →+* FractionRing R[X] :=
  IsFractionRing.map (j := (Polynomial.C : R →+* R[X])) Polynomial.C_injective

theorem coeffMap_algebraMap (a : R) : coeffMap (algebraMap R (FractionRing R) a) =
    algebraMap R[X] (FractionRing R[X]) (C a) := by
  rw [coeffMap, IsFractionRing.map, IsLocalization.map_eq]

theorem frac_rep (c : FractionRing R) : ∃ u v : R, v ≠ 0 ∧
    c * algebraMap R (FractionRing R) v = algebraMap R (FractionRing R) u := by
  obtain ⟨x, hx⟩ := IsLocalization.surj (nonZeroDivisors R) c
  refine ⟨x.1, x.2, ?_, hx⟩
  exact (mem_nonZeroDivisors_iff_ne_zero).mp x.2.property

theorem coeffMap_frac_rep (c : FractionRing R) : ∃ u v : R, v ≠ 0 ∧
    coeffMap c = (algebraMap R[X] (FractionRing R[X]) (C u)) /
      (algebraMap R[X] (FractionRing R[X]) (C v)) := by
  obtain ⟨u, v, hv, hc⟩ := frac_rep c
  refine ⟨u, v, hv, ?_⟩
  have h := congrArg coeffMap hc
  rw [map_mul, coeffMap_algebraMap, coeffMap_algebraMap] at h
  have hden : algebraMap R[X] (FractionRing R[X]) (C v) ≠ 0 := by
    intro hz
    apply Polynomial.C_ne_zero.mpr hv
    exact (IsFractionRing.injective (R[X]) (FractionRing R[X])) (by simpa using hz)
  exact (eq_div_iff hden).2 h
theorem scalar_mul_derivative_ne_zero (p : R[X]) (hp : p ≠ 0)
    (u v : R) (hu : u ≠ 0) (hv : v ≠ 0) :
    C u * p + C v * p.derivative ≠ 0 := by
  have hleft : C u * p ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hu) hp
  have hdegree : (C v * p.derivative).degree < (C u * p).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hv,
      Polynomial.degree_mul, Polynomial.degree_C hu]
    simpa using Polynomial.degree_derivative_lt hp
  have hsumDegree := Polynomial.degree_add_eq_left_of_degree_lt hdegree
  intro h
  have hzero : (C u * p + C v * p.derivative).degree = ⊥ := by simp [h]
  rw [hsumDegree] at hzero
  exact (Polynomial.degree_ne_bot.mpr hleft) hzero

theorem fractionConstant_add_fiberSum_ne_zero (s : Finset R)
    (c : FractionRing R) (hc : c ≠ 0) :
    coeffMap c + ∑ a ∈ s,
      (algebraMap R[X] (FractionRing R[X]) (X + C a))⁻¹ ≠ 0 := by
  rw [sum_inverse_linearFactors_eq_logDerivative]
  obtain ⟨u, v, hv, hrepr⟩ := coeffMap_frac_rep c
  let P := rootProduct s
  have hP : P ≠ 0 := (rootProduct_monic s).ne_zero
  have hpMap : algebraMap R[X] (FractionRing R[X]) P ≠ 0 := fraction_map_poly_ne_zero hP
  have hvMap : algebraMap R[X] (FractionRing R[X]) (C v) ≠ 0 := by
    intro hz
    apply Polynomial.C_ne_zero.mpr hv
    exact (IsFractionRing.injective (R[X]) (FractionRing R[X])) (by simpa using hz)
  have hnum : coeffMap c * algebraMap R[X] (FractionRing R[X]) (C v) =
      algebraMap R[X] (FractionRing R[X]) (C u) := (eq_div_iff hvMap).1 hrepr
  have hu : u ≠ 0 := by
    intro hu0
    have hcMap : coeffMap c = 0 := by
      rw [hrepr, hu0]
      simp
    apply hc
    exact (RingHom.injective (coeffMap (R := R))) (by simpa using hcMap)
  intro hz
  have hscaled : coeffMap c * algebraMap R[X] (FractionRing R[X]) P +
      algebraMap R[X] (FractionRing R[X]) P.derivative = 0 := by
    have h := congrArg (fun z : FractionRing R[X] =>
        z * algebraMap R[X] (FractionRing R[X]) P) hz
    dsimp [P] at h ⊢
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hpMap, mul_one, zero_mul] at h
    exact h
  have hnumscaled :
      algebraMap R[X] (FractionRing R[X]) (C u) *
          algebraMap R[X] (FractionRing R[X]) P +
        algebraMap R[X] (FractionRing R[X]) (C v) *
          algebraMap R[X] (FractionRing R[X]) P.derivative = 0 := by
    calc
      _ = (coeffMap c * algebraMap R[X] (FractionRing R[X]) (C v)) *
            algebraMap R[X] (FractionRing R[X]) P +
          (algebraMap R[X] (FractionRing R[X]) P.derivative) *
            algebraMap R[X] (FractionRing R[X]) (C v) := by rw [← hnum]; ring
      _ = (coeffMap c * algebraMap R[X] (FractionRing R[X]) P +
            algebraMap R[X] (FractionRing R[X]) P.derivative) *
            algebraMap R[X] (FractionRing R[X]) (C v) := by ring
      _ = 0 := by rw [hscaled]; simp
  have hpolyMap : algebraMap R[X] (FractionRing R[X])
      (C u * P + C v * P.derivative) = 0 := by
    rw [map_add, map_mul, map_mul]
    simpa [coeffMap_algebraMap] using hnumscaled
  have hpoly : C u * P + C v * P.derivative = 0 := by
    apply (IsFractionRing.injective (R[X]) (FractionRing R[X]))
    simpa using hpolyMap
  exact (scalar_mul_derivative_ne_zero P hP u v hu hv) hpoly

#print axioms sum_inverse_linearFactors_eq_logDerivative
#print axioms coeffMap_frac_rep
#print axioms scalar_mul_derivative_ne_zero
#print axioms fractionConstant_add_fiberSum_ne_zero

end Carlet.CandidatePaper.Section32IntegralDomainFiber







