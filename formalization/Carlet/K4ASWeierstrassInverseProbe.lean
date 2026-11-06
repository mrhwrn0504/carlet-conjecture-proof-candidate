import Carlet.K4ASWeierstrassCurveProbe
import Mathlib.FieldTheory.Finite.Basic

namespace Carlet

variable {K : Type*} [Field K] [CharP K 2]

theorem k4ASWeierstrass_inverse_denominator_factor
    (A B x δ : K) (hx : x ≠ 0) :
    (k4ASD x)^2*δ+B*x^2*k4ASD x+
      A*x*(x+1)*k4ASD x+A^2*x^2*k4ASD x =
      k4ASD x*x^2*(k4ASWeierstrassX A x δ+k4ASC A B) := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K)=1 := by
    calc
      (3 : K) = (2 : K)+1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have h4 : (4 : K)=0 := by
    calc
      (4 : K) = (2 : K)*(2 : K) := by norm_num
      _ = 0 := by rw [h2]; simp
  dsimp [k4ASD,k4ASWeierstrassX,k4ASNX,k4ASC]
  field_simp [hx]
  ring_nf
  simp [h2,h3,h4]

theorem k4ASWeierstrass_inverse_denominator_ne_zero
    (A B x δ : K) (hx : x ≠ 0)
    (hD : k4ASD x ≠ 0)
    (hXC : k4ASWeierstrassX A x δ+k4ASC A B ≠ 0) :
    (k4ASD x)^2*δ+B*x^2*k4ASD x+
      A*x*(x+1)*k4ASD x+A^2*x^2*k4ASD x ≠ 0 := by
  rw [k4ASWeierstrass_inverse_denominator_factor A B x δ hx]
  exact mul_ne_zero (mul_ne_zero hD (pow_ne_zero 2 hx)) hXC

theorem k4ASWeierstrass_exceptional_affine_point (A B : K) :
    (k4ASWeierstrassCurve A B).toAffine.Equation
      (A^2+B) (A+(A^2+B)) := by
  rw [k4ASWeierstrassCurve_equation]
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K)=1 := by
    calc
      (3 : K) = (2 : K)+1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have h4 : (4 : K)=0 := by
    calc
      (4 : K) = (2 : K)*(2 : K) := by norm_num
      _ = 0 := by rw [h2]; simp
  have h5 : (5 : K)=1 := by
    calc
      (5 : K) = (4 : K)+1 := by norm_num
      _ = 1 := by rw [h4]; simp
  have h6 : (6 : K)=0 := by
    calc
      (6 : K) = (2 : K)*(3 : K) := by norm_num
      _ = 0 := by rw [h2]; simp
  ring_nf
  simp [h2,h3,h4,h5,h6]

theorem k4ASAS_D_zero_fiber_iff
    (A B x δ : K) (hD : k4ASD x = 0) :
    (k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x) ↔
      B*x+A+B=0 := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  have hx2 : x^2=x+1 := by
    dsimp [k4ASD] at hD
    linear_combination hD + (-1-x)*h2
  constructor
  · intro hcurve
    have hrhs : (A+B)*x^2+A*x=0 := by
      rw [hD] at hcurve
      simpa using hcurve.symm
    rw [hx2] at hrhs
    linear_combination hrhs + (-A*x)*h2
  · intro hparam
    rw [hD]
    rw [hx2]
    linear_combination hparam + (-A-A*x-B-B*x)*h2

theorem k4ASD_ne_zero_of_odd_card_exponent
    [Fintype K] (n : ℕ) (hn : Odd n)
    (hcard : Fintype.card K = 2^n) (x : K) :
    k4ASD x ≠ 0 := by
  intro hD
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K)=1 := by
    calc
      (3 : K) = (2 : K)+1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have hx2 : x^2=x+1 := by
    dsimp [k4ASD] at hD
    linear_combination hD + (-1-x)*h2
  have hx1 : x ≠ 1 := by
    intro h
    subst x
    dsimp [k4ASD] at hD
    norm_num [h2] at hD
    rw [h3] at hD
    exact one_ne_zero hD
  have hx3 : x^3=1 := by
    calc
      x^3 = x^2*x := by ring
      _ = (x+1)*x := by rw [hx2]
      _ = x^2+x := by ring
      _ = (x+1)+x := by rw [hx2]
      _ = 1 := by linear_combination x*h2
  obtain ⟨m, rfl⟩ := hn
  have hx4 : x^4=x := by
    calc
      x^4 = (x^2)^2 := by ring
      _ = (x+1)^2 := by rw [hx2]
      _ = x^2+1 := by linear_combination x*h2
      _ = x := by rw [hx2]; linear_combination h2
  have hxplus4 : (x+1)^4=x+1 := by
    have hsquare : (x+1)^2=x^2+1 := by linear_combination x*h2
    calc
      (x+1)^4 = ((x+1)^2)^2 := by ring
      _ = (x^2+1)^2 := by rw [hsquare]
      _ = x^4+1 := by linear_combination x^2*h2
      _ = x+1 := by rw [hx4]
  have hcycle : ∀ r : ℕ, x^(2^(2*r+1))=x+1 := by
    intro r
    induction r with
    | zero => simpa using hx2
    | succ r ih =>
        have hexp : 2^(2*(r+1)+1)=2^(2*r+1)*4 := by
          rw [show 2*(r+1)+1=(2*r+1)+2 by omega, pow_add]
          norm_num
        rw [hexp, pow_mul, ih, hxplus4]
  have hp := FiniteField.pow_card x
  rw [hcard, hcycle m] at hp
  have hone : (1 : K)=0 := by
    calc
      1 = (x+1)-x := by ring
      _ = x-x := by rw [hp]
      _ = 0 := by ring
  exact one_ne_zero hone

theorem k4ASD_ne_zero_of_odd_finrank
    [Fintype K] [Algebra (ZMod 2) K] (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K = n) (x : K) :
    k4ASD x ≠ 0 := by
  apply k4ASD_ne_zero_of_odd_card_exponent n hn ?_ x
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  simpa only [ZMod.card, hfinrank] using hcard

theorem k4AS_x_zero_fiber (A B δ : K) :
    k4ASH A B 0 δ = 0 ↔ δ=0 ∨ δ=1 := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    have h' : δ*(δ+1)=0 := by
      dsimp [k4ASH,k4ASD] at h
      linear_combination h
    rcases mul_eq_zero.mp h' with hδ | hδ
    · exact Or.inl hδ
    · right
      have hδone : δ=1 := by linear_combination hδ-h2
      exact hδone
  · rintro (rfl | hδ)
    · simp [k4ASH,k4ASD]
    · subst δ
      dsimp [k4ASH,k4ASD]
      linear_combination h2

#print axioms k4ASWeierstrass_inverse_denominator_factor
#print axioms k4ASWeierstrass_inverse_denominator_ne_zero
#print axioms k4ASAS_D_zero_fiber_iff
#print axioms k4ASD_ne_zero_of_odd_card_exponent
#print axioms k4ASD_ne_zero_of_odd_finrank
#print axioms k4AS_x_zero_fiber

end Carlet
