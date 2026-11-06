import Carlet.K4SymmetryProbe
import Carlet.KloostermanThree
import Carlet.K4PoleNumerator

noncomputable section
open scoped BigOperators
open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def k4ASFiber (g : K → K) :=
  Σ t : {x : K // x ∈ k4Admissible (K := K)},
    {y : K // y^2 + y = g t.1 / k4Denominator t.1}

noncomputable instance k4ASFiberFintype (g : K → K) : Fintype (k4ASFiber (K := K) g) := by
  classical
  unfold k4ASFiber
  infer_instance

theorem k4_as_fiber_card (g : K → K) :
    (Fintype.card (k4ASFiber (K := K) g) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), traceCharacter (g t / k4Denominator t) := by
  classical
  unfold k4ASFiber
  rw [Fintype.card_sigma, Nat.cast_sum]
  simp_rw [artinSchreier_fiber_card]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_coe_sort (k4Admissible (K := K)) (fun _ : K => (1 : ℝ)),
    Finset.sum_coe_sort (k4Admissible (K := K))
      (fun t => traceCharacter (g t / k4Denominator t))]
  simp

theorem k4_as_fiber_card_sign0 :
    (Fintype.card (k4ASFiber (K := K) fun _ => (1 : K)) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), k4Sign0 t := by
  simpa [k4Sign0] using (k4_as_fiber_card (K := K) (fun _ => (1 : K)))

theorem k4_as_fiber_card_sign1 :
    (Fintype.card (k4ASFiber (K := K) fun t => (t^2+t)^2) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), k4Sign1 t := by
  simpa [k4Sign1] using (k4_as_fiber_card (K := K) (fun t => (t^2+t)^2))

theorem k4_as_fiber_card_sign2 :
    (Fintype.card (k4ASFiber (K := K) fun t => t^6) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), k4Sign2 t := by
  simpa [k4Sign2] using (k4_as_fiber_card (K := K) (fun t => t^6))

def k4PolynomialCurvePoints (N : Polynomial K) :=
  {p : K × K // Polynomial.eval p.1 (k4PoleDenPoly K) * (p.2^2+p.2) =
    Polynomial.eval p.1 N}

omit [Fintype K] [DecidableEq K] in
lemma k4_denominator_eval_eq (t : K) :
    k4Denominator t = Polynomial.eval t (k4PoleDenPoly K) := by
  simpa [k4Denominator, k4PoleDenominator] using
    (k4_pole_den_eval_eq (K := K) t)

noncomputable instance k4PolynomialCurvePointsFintype (N : Polynomial K) :
    Fintype (k4PolynomialCurvePoints (K := K) N) := by
  classical
  unfold k4PolynomialCurvePoints
  infer_instance

noncomputable def k4_polynomial_curve_equiv (N U V : Polynomial K)
    (hbez : U * k4PoleDenPoly K + V * N = 1) :
    k4ASFiber (K := K) (fun t => Polynomial.eval t N) ≃
      k4PolynomialCurvePoints (K := K) N := by
  classical
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨t, ht⟩, ⟨y, hy⟩⟩
    have hd0 : k4Denominator t ≠ 0 := (Finset.mem_filter.mp ht).2
    have hd : Polynomial.eval t (k4PoleDenPoly K) ≠ 0 := by
      rw [← k4_denominator_eval_eq]
      exact hd0
    refine ⟨(t, y), ?_⟩
    change Polynomial.eval t (k4PoleDenPoly K) * (y^2+y) = Polynomial.eval t N
    rw [k4_denominator_eval_eq] at hy
    rw [hy]
    field_simp [hd]
  · rintro ⟨⟨t, y⟩, hcurve⟩
    have hd : Polynomial.eval t (k4PoleDenPoly K) ≠ 0 := by
      intro hzero
      have hnzero : Polynomial.eval t N = 0 := by
        have h := hcurve
        rw [hzero] at h
        simpa using h.symm
      have h_eval := congrArg (Polynomial.eval t) hbez
      rw [Polynomial.eval_add, Polynomial.eval_mul] at h_eval
      simp [hzero, hnzero] at h_eval
    have hd0 : k4Denominator t ≠ 0 := by
      rw [k4_denominator_eval_eq]
      exact hd
    have ht : t ∈ k4Admissible (K := K) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0⟩
    have hy : y^2+y = Polynomial.eval t N / k4Denominator t := by
      rw [k4_denominator_eval_eq]
      calc
        y^2+y = Polynomial.eval t (k4PoleDenPoly K) * (y^2+y) /
            Polynomial.eval t (k4PoleDenPoly K) := by field_simp
        _ = Polynomial.eval t N / Polynomial.eval t (k4PoleDenPoly K) := by rw [hcurve]
    exact ⟨⟨t, ht⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨t, ht⟩, ⟨y, hy⟩⟩
    rfl
  · rintro ⟨⟨t, y⟩, hcurve⟩
    rfl

theorem k4_polynomial_curve_card (N U V : Polynomial K)
    (hbez : U * k4PoleDenPoly K + V * N = 1) :
    (Fintype.card (k4PolynomialCurvePoints (K := K) N) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K),
          traceCharacter (Polynomial.eval t N / k4Denominator t) := by
  rw [← Fintype.card_congr (k4_polynomial_curve_equiv (K := K) N U V hbez)]
  exact k4_as_fiber_card (K := K) (fun t => Polynomial.eval t N)

theorem k4_polynomial_curve_card_sign0 :
    (Fintype.card (k4PolynomialCurvePoints (K := K) 1) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), k4Sign0 t := by
  simpa [k4Sign0] using
    (k4_polynomial_curve_card (K := K) (1 : Polynomial K) 0 1 (by simp))

theorem k4_polynomial_curve_card_sign1 :
    (Fintype.card
      (k4PolynomialCurvePoints (K := K) (k4PoleNumOnePoly K)) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), k4Sign1 t := by
  have h := k4_pole_num_one_bezout (K := K)
  simpa [k4Sign1, k4_pole_num_one_eval] using
    (k4_polynomial_curve_card (K := K) (k4PoleNumOnePoly K)
      (X^2+X+1) (X^4+X+1) h.symm)

omit [Fintype K] [DecidableEq K] in
lemma k4_num02_trace_eq (t : K) :
    traceCharacter (Polynomial.eval t (k4PoleNum02Poly K) / k4Denominator t) =
      k4Sign0 t * k4Sign2 t := by
  rw [k4_pole_num02_eval, add_div, AddChar.map_add_eq_mul]
  simp only [k4Sign0, k4Sign2]
  ring

theorem k4_polynomial_curve_card_sign02 :
    (Fintype.card
      (k4PolynomialCurvePoints (K := K) (k4PoleNum02Poly K)) : ℝ) =
      (k4Admissible (K := K)).card +
        ∑ t ∈ k4Admissible (K := K), k4Sign0 t * k4Sign2 t := by
  have h := k4_pole_num02_bezout (K := K)
  have hc := k4_polynomial_curve_card (K := K) (k4PoleNum02Poly K)
    (X^5+X^4+X^3+X^2+X) (X^5+X^3+X+1) h.symm
  simpa only [k4_num02_trace_eq] using hc

#print axioms k4_as_fiber_card
#print axioms k4_as_fiber_card_sign0
#print axioms k4_as_fiber_card_sign1
#print axioms k4_as_fiber_card_sign2
#print axioms k4_polynomial_curve_equiv
#print axioms k4_polynomial_curve_card
#print axioms k4_polynomial_curve_card_sign0
#print axioms k4_polynomial_curve_card_sign1
#print axioms k4_polynomial_curve_card_sign02

end Carlet
