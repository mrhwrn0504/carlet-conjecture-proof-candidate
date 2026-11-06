import Mathlib.Tactic

noncomputable section

/-- The parameter produced by adjoining t² to the span of 1 and t. -/
theorem k4_extension_parameter {K : Type*} [Field K] [CharP K 2] (t : K) :
    ((t^2)^2+t^2)^2 + (t^2+t)*((t^2)^2+t^2) =
      (t^2+t)^3*((t^2+t)+1) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by
    calc
      (3 : K) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have h4 : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  have h7 : (7 : K) = 1 := by
    calc
      (7 : K) = 3 + 4 := by norm_num
      _ = 1 := by rw [h3, h4]; simp
  ring_nf
  simp [h2, h3, h4, h7]

/-- The coefficient of X² in the third subspace-polynomial extension. -/
theorem k4_second_coefficient_factor {K : Type*} [Field K] [CharP K 2] (u : K) :
    u^2 + (u^3*(u+1))*(1+u) = u^2*(u^3+u+1) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ring_nf
  simp [h2]

theorem k4_second_trace_polynomial {K : Type*} [Field K] [CharP K 2] (t : K) :
    t^2*(t^2+t)*((t^2+t)+1) = (t^3)^2+t^3 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ring_nf
  simp [h2]

/-- Algebraic composition underlying the 1,t,t² construction. -/
theorem k4_artin_schreier_chain {K : Type*} [Field K]
    (u z s v : K)
    (hz : z^2 + z = 1 / (u^3 + u + 1))
    (hs : s^2 + s = u*(u+1)*z)
    (hv : v^2 + v = u*s) :
    ((v^2+v)^2 + u*(v^2+v))^2 +
      (u^3*(u+1))*((v^2+v)^2 + u*(v^2+v)) =
        (u^3*(u+1))^2 / (u^3+u+1) := by
  have hL2 : (v^2+v)^2 + u*(v^2+v) = (u^3*(u+1))*z := by
    rw [hv]
    calc
      (u*s)^2 + u*(u*s) = u^2*(s^2+s) := by ring
      _ = u^2*(u*(u+1)*z) := by rw [hs]
      _ = (u^3*(u+1))*z := by ring
  rw [hL2]
  calc
    ((u^3*(u+1))*z)^2 + (u^3*(u+1))*((u^3*(u+1))*z) =
        (u^3*(u+1))^2*(z^2+z) := by ring
    _ = (u^3*(u+1))^2*(1 / (u^3+u+1)) := by rw [hz]
    _ = (u^3*(u+1))^2 / (u^3+u+1) := by ring

/-- The chained target equals the coefficient ratio when u is nonzero. -/
theorem k4_coefficient_ratio_factor {K : Type*} [Field K]
    (u : K) (hu : u ≠ 0) :
    (u^4*(u+1))^2 / (u^2*(u^3+u+1)) =
      (u^3*(u+1))^2 / (u^3+u+1) := by
  field_simp

#print axioms k4_artin_schreier_chain
#print axioms k4_coefficient_ratio_factor
#print axioms k4_extension_parameter
#print axioms k4_second_coefficient_factor
#print axioms k4_second_trace_polynomial
