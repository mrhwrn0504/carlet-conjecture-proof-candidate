import Carlet.K4SpecializationHProbe
import Carlet.K4HLinearRootProbe
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

/-- Specialize (x,y,z) to (X,1,aX+b) after scalar extension. -/
def k4HLineEval (a b : K) : Hring →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap (ZMod 2) K))
    ![Polynomial.X, 1, Polynomial.C a * Polynomial.X + Polynomial.C b]

theorem k4HLineEval_H (a b : K) :
    k4HLineEval K a b k4H = k4HLinearTest K a b := by
  simp [k4HLineEval, k4H, k4HLinearTest, MvPolynomial.eval₂Hom]

/-- For all a,b over any characteristic-two field, H does not vanish
    identically on the line z=ax+by. -/
theorem k4HLineEval_H_ne_zero (a b : K) : k4HLineEval K a b k4H ≠ 0 := by
  rw [k4HLineEval_H]
  exact k4HLinearTest_ne_zero K a b

def k4HOver : MvPolynomial (Fin 3) K := k4H.map (algebraMap (ZMod 2) K)

def k4HLineEvalOver (a b : K) : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X, 1, Polynomial.C a * Polynomial.X + Polynomial.C b]

theorem k4HLineEvalOver_H (a b : K) :
    k4HLineEvalOver K a b (k4HOver K) = k4HLinearTest K a b := by
  simp [k4HLineEvalOver, k4HOver, k4H, k4HLinearTest, MvPolynomial.eval₂Hom]

theorem k4H_no_linear_factor_z (a b : K) :
    ¬ (MvPolynomial.X 2 + MvPolynomial.C a * MvPolynomial.X 0 +
        MvPolynomial.C b * MvPolynomial.X 1) ∣ k4HOver K := by
  intro hdiv
  obtain ⟨r, hr⟩ := hdiv
  have he := congrArg (k4HLineEvalOver K a b) hr
  rw [map_mul, k4HLineEvalOver_H] at he
  have hzero : k4HLineEvalOver K a b
      (MvPolynomial.X 2 + MvPolynomial.C a * MvPolynomial.X 0 +
        MvPolynomial.C b * MvPolynomial.X 1) = 0 := by
    simp [k4HLineEvalOver, MvPolynomial.eval₂Hom]
    have h2 : (2 : Polynomial K) = 0 := by
      have : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
      exact CharP.cast_eq_zero (Polynomial K) 2
    linear_combination (Polynomial.C a * Polynomial.X + Polynomial.C b) * h2
  rw [hzero, zero_mul] at he
  exact k4HLinearTest_ne_zero K a b he

def k4HVerticalEval (a : K) : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C a, 1, Polynomial.X]

theorem k4HVerticalEval_H_normal (a : K) :
    k4HVerticalEval K a (k4HOver K) = Polynomial.X^4 +
      Polynomial.C (a^2+a+1) * Polynomial.X^2 +
      Polynomial.C (a*(a+1)) * Polynomial.X + Polynomial.C (a^4+a^2+1) := by
  simp [k4HVerticalEval, k4HOver, k4H, MvPolynomial.eval₂Hom]
  ring

theorem k4HVerticalEval_H_ne_zero (a : K) :
    k4HVerticalEval K a (k4HOver K) ≠ 0 := by
  intro he
  have hc := congrArg (fun p : Polynomial K => p.coeff 4) he
  rw [k4HVerticalEval_H_normal] at hc
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hc
  norm_num at hc

theorem k4H_no_linear_factor_x (a : K) :
    ¬ (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1) ∣ k4HOver K := by
  intro hdiv
  obtain ⟨r, hr⟩ := hdiv
  have he := congrArg (k4HVerticalEval K a) hr
  rw [map_mul] at he
  have hzero : k4HVerticalEval K a
      (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1) = 0 := by
    simp [k4HVerticalEval, MvPolynomial.eval₂Hom]
    have : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
    have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero (Polynomial K) 2
    linear_combination Polynomial.C a * h2
  rw [hzero, zero_mul] at he
  exact k4HVerticalEval_H_ne_zero K a he

theorem k4H_no_linear_factor_y : ¬ MvPolynomial.X 1 ∣ k4HOver K := by
  intro hdiv
  obtain ⟨r, hr⟩ := hdiv
  let e : MvPolynomial (Fin 3) K →+* K :=
    MvPolynomial.eval₂Hom (RingHom.id K) ![1, 0, 0]
  have he := congrArg e hr
  simp [e, k4HOver, k4H, MvPolynomial.eval₂Hom] at he

theorem k4H_no_nonzero_homogeneous_linear_factor (a b c : K)
    (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ¬ (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 +
       MvPolynomial.C c * MvPolynomial.X 2) ∣ k4HOver K := by
  intro hd
  by_cases hc : c = 0
  · by_cases ha : a = 0
    · have hb : b ≠ 0 := by simpa [ha, hc] using habc
      apply k4H_no_linear_factor_y K
      apply dvd_trans ?_ hd
      refine ⟨MvPolynomial.C b, ?_⟩
      simp only [ha, hc, map_zero, zero_mul, zero_add, add_zero]
      ring
    · apply k4H_no_linear_factor_x K (a⁻¹ * b)
      apply dvd_trans ?_ hd
      refine ⟨MvPolynomial.C a, ?_⟩
      have hab : (MvPolynomial.C a : MvPolynomial (Fin 3) K) *
          MvPolynomial.C (a⁻¹*b) = MvPolynomial.C b := by
        rw [← map_mul]
        simp [ha]
      simp only [hc, map_zero, zero_mul, add_zero]
      calc
        (MvPolynomial.C a : MvPolynomial (Fin 3) K) * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 =
          MvPolynomial.C a * MvPolynomial.X 0 +
            (MvPolynomial.C a * MvPolynomial.C (a⁻¹*b)) * MvPolynomial.X 1 := by rw [hab]
        _ = (MvPolynomial.X 0 + MvPolynomial.C (a⁻¹*b) * MvPolynomial.X 1) *
            MvPolynomial.C a := by ring
  · apply k4H_no_linear_factor_z K (c⁻¹ * a) (c⁻¹ * b)
    apply dvd_trans ?_ hd
    refine ⟨MvPolynomial.C c, ?_⟩
    have hca : (MvPolynomial.C c : MvPolynomial (Fin 3) K) *
        MvPolynomial.C (c⁻¹*a) = MvPolynomial.C a := by
      rw [← map_mul]
      simp [hc]
    have hcb : (MvPolynomial.C c : MvPolynomial (Fin 3) K) *
        MvPolynomial.C (c⁻¹*b) = MvPolynomial.C b := by
      rw [← map_mul]
      simp [hc]
    calc
      (MvPolynomial.C a : MvPolynomial (Fin 3) K) * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 +
          MvPolynomial.C c * MvPolynomial.X 2 =
        (MvPolynomial.C c * MvPolynomial.C (c⁻¹*a)) * MvPolynomial.X 0 +
        (MvPolynomial.C c * MvPolynomial.C (c⁻¹*b)) * MvPolynomial.X 1 +
          MvPolynomial.C c * MvPolynomial.X 2 := by rw [hca, hcb]
      _ = (MvPolynomial.X 2 + MvPolynomial.C (c⁻¹*a) * MvPolynomial.X 0 +
          MvPolynomial.C (c⁻¹*b) * MvPolynomial.X 1) * MvPolynomial.C c := by ring

#print axioms k4H_no_nonzero_homogeneous_linear_factor
#print axioms k4H_no_linear_factor_y
#print axioms k4H_no_linear_factor_x
#print axioms k4H_no_linear_factor_z
#print axioms k4HLineEval_H
#print axioms k4HLineEval_H_ne_zero
end Carlet
