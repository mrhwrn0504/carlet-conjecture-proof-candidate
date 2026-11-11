import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Carlet.Elementary

/-!
Logarithmic-derivative identity needed for the candidate paper's proof that
the Carlet section is nonzero. This is the field-valued polynomial identity
for a finite family of distinct linear factors, formalized without assuming
the geometric conclusions of the manuscript.
-/

noncomputable section

namespace Carlet.CandidatePaper.RationalFunctionLogDerivative

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem rootProduct_monic (s : Finset K) : (Carlet.rootProduct s).Monic := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Carlet.rootProduct]
  | @insert a s ha ih =>
      have hprod : Carlet.rootProduct (insert a s) =
          (X + C a) * Carlet.rootProduct s := by
        simp [Carlet.rootProduct, ha]
      rw [hprod]
      exact (monic_X_add_C a).mul ih

theorem rootProduct_natDegree (s : Finset K) :
    (Carlet.rootProduct s).natDegree = s.card := by
  classical
  rw [Carlet.rootProduct, Polynomial.natDegree_prod]
  · simp
  · intro a ha
    exact (monic_X_add_C a).ne_zero

theorem rootProduct_derivative_natDegree_lt (s : Finset K) (hs : s.Nonempty) :
    (Carlet.rootProduct s).derivative.natDegree <
      (Carlet.rootProduct s).natDegree := by
  apply Polynomial.natDegree_derivative_lt
  rw [rootProduct_natDegree]
  exact Nat.ne_of_gt (Finset.card_pos.mpr hs)

/-- A nonzero scalar multiple of a nonzero polynomial cannot be canceled by
its strictly lower-degree derivative. This is the leading-term step in the
candidate paper's nonvanishing argument. -/
theorem scalar_mul_add_derivative_ne_zero (p : K[X]) (hp : p ≠ 0)
    (c : K) (hc : c ≠ 0) : C c * p + p.derivative ≠ 0 := by
  have hscalar : C c * p ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hp
  have hdegree : p.derivative.degree < (C c * p).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc]
    simpa using Polynomial.degree_derivative_lt hp
  have hsumDegree := Polynomial.degree_add_eq_left_of_degree_lt hdegree
  intro h
  have hzero : (C c * p + p.derivative).degree = ⊥ := by simp [h]
  rw [hsumDegree] at hzero
  exact (Polynomial.degree_ne_bot.mpr hscalar) hzero

theorem fraction_map_poly_ne_zero {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (FractionRing K[X]) p ≠ 0 := by
  intro h
  apply hp
  exact (IsFractionRing.injective (K[X]) (FractionRing K[X])) (by simpa using h)

theorem fraction_scalar_mul_add_derivative_ne_zero (p : K[X]) (hp : p ≠ 0)
    (c : K) (hc : c ≠ 0) :
    algebraMap K[X] (FractionRing K[X]) (C c * p + p.derivative) ≠ 0 :=
  fraction_map_poly_ne_zero (scalar_mul_add_derivative_ne_zero p hp c hc)

/-- A nonzero constant plus a logarithmic derivative cannot vanish: clearing
the denominator produces a nonzero scalar multiple of the polynomial plus its
strictly lower-degree derivative. -/
theorem scalar_add_logDerivative_ne_zero (p : K[X]) (hp : p ≠ 0)
    (c : K) (hc : c ≠ 0) :
    algebraMap K[X] (FractionRing K[X]) (C c) +
      algebraMap K[X] (FractionRing K[X]) (p.derivative) *
        (algebraMap K[X] (FractionRing K[X]) p)⁻¹ ≠ 0 := by
  let R : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) p
  let C₀ : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) (C c)
  let D : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) p.derivative
  have hR : R ≠ 0 := fraction_map_poly_ne_zero hp
  intro h
  have hmul := congrArg (fun z : FractionRing K[X] => z * R) h
  have hcleared : C₀ * R + D = 0 := by
    dsimp [R, C₀, D] at hmul ⊢
    rw [add_mul, mul_assoc, inv_mul_cancel₀ (fraction_map_poly_ne_zero hp), mul_one,
      zero_mul] at hmul
    exact hmul
  have hpoly : algebraMap K[X] (FractionRing K[X]) (C c * p + p.derivative) = 0 := by
    rw [map_add, map_mul]
    simpa [C₀, R, D] using hcleared
  exact fraction_scalar_mul_add_derivative_ne_zero p hp c hc hpoly

/-- Sum of inverses of the linear factors `X + a` equals the logarithmic
derivative of their product in the rational function field. -/
theorem sum_inverse_linearFactors_eq_logDerivative (s : Finset K) :
    (∑ a ∈ s, (algebraMap K[X] (FractionRing K[X]) (X + C a))⁻¹) =
      algebraMap K[X] (FractionRing K[X]) ((Carlet.rootProduct s).derivative) *
        (algebraMap K[X] (FractionRing K[X]) (Carlet.rootProduct s))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Carlet.rootProduct]
  | @insert a s ha ih =>
      have hprod : Carlet.rootProduct (insert a s) =
          (X + C a) * Carlet.rootProduct s := by
        simp [Carlet.rootProduct, ha]
      have hderiv : (Carlet.rootProduct (insert a s)).derivative =
          Carlet.rootProduct s + (X + C a) * (Carlet.rootProduct s).derivative := by
        rw [hprod, derivative_mul, derivative_X_add_C]
        simp
      let A : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) (X + C a)
      let B : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) (Carlet.rootProduct s)
      let C' : FractionRing K[X] := algebraMap K[X] (FractionRing K[X])
        ((Carlet.rootProduct s).derivative)
      have hA : algebraMap K[X] (FractionRing K[X]) (X + C a) ≠ 0 :=
        fraction_map_poly_ne_zero (monic_X_add_C a).ne_zero
      have hB : algebraMap K[X] (FractionRing K[X]) (Carlet.rootProduct s) ≠ 0 :=
        fraction_map_poly_ne_zero (rootProduct_monic s).ne_zero
      have hA' : A ≠ 0 := by simpa [A] using hA
      have hB' : B ≠ 0 := by simpa [B] using hB
      have hderiv_map : algebraMap K[X] (FractionRing K[X])
          ((Carlet.rootProduct (insert a s)).derivative) = B + A * C' := by
        rw [hderiv, map_add, map_mul]
      have hprod_map : algebraMap K[X] (FractionRing K[X])
          (Carlet.rootProduct (insert a s)) = A * B := by
        rw [hprod, map_mul]
      rw [Finset.sum_insert ha, hderiv_map, hprod_map, ih]
      change A⁻¹ + C' * B⁻¹ = (B + A * C') * (A * B)⁻¹
      field_simp [hA', hB']

#print axioms rootProduct_monic
#print axioms rootProduct_natDegree
#print axioms rootProduct_derivative_natDegree_lt
#print axioms scalar_mul_add_derivative_ne_zero
#print axioms fraction_map_poly_ne_zero
#print axioms fraction_scalar_mul_add_derivative_ne_zero
#print axioms scalar_add_logDerivative_ne_zero
#print axioms sum_inverse_linearFactors_eq_logDerivative

end Carlet.CandidatePaper.RationalFunctionLogDerivative
