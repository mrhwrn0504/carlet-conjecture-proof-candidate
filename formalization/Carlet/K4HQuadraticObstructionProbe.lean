import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- Coefficient obstruction for a putative homogeneous quadratic factorization
    of H. The hypotheses are exact consequences of comparing coefficients. -/
theorem k4H_quadratic_coefficient_obstruction (a b c d e : K)
    (ha : a^3+a = 0) (hb : b^3+b = 0)
    (hmix : a+b+a^2*b = 1)
    (hc4 : c*(c+(1+a^2)) = 1) (hc3 : c+d*(1+a^2)=0)
    (he4 : e*(e+(1+b^2)) = 1) (he3 : e+d*(1+b^2)=0) : False := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by linear_combination h2
  have hcases (x : K) (hx : x^3+x = 0) : x = 0 ∨ x = 1 := by
    have hm : x*(x+1)^2 = 0 := by linear_combination hx + x^2*h2
    rcases mul_eq_zero.mp hm with hz | hz
    · exact Or.inl hz
    · have hz' : x+1 = 0 := by
        have hh : (x+1)*(x+1) = 0 := by simpa [pow_two] using hz
        exact (mul_eq_zero.mp hh).elim id id
      right
      linear_combination hz' - h2
  rcases hcases a ha with ha0 | ha1 <;> rcases hcases b hb with hb0 | hb1
  · simp [ha0, hb0] at hmix
  · rw [hb1] at he3 he4
    simp [h11] at he3 he4
    rw [he3] at he4
    simp at he4
  · rw [ha1] at hc3 hc4
    simp [h11] at hc3 hc4
    rw [hc3] at hc4
    simp at hc4
  · rw [ha1] at hc3 hc4
    simp [h11] at hc3 hc4
    rw [hc3] at hc4
    simp at hc4

#print axioms k4H_quadratic_coefficient_obstruction
end Carlet
