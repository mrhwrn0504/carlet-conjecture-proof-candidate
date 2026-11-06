import Mathlib.Tactic

noncomputable section

namespace Carlet

/-- The 15 nontrivial Fourier coefficients bounded by `2 * sqrt q` imply
    that the norm-one incidence count is greater than two for q ≥ 2^10.
    This is the numerical step in the genus-one alternative to the much larger
    Lang–Weil threshold; it does not establish the required curve bound. -/
theorem k4_normOne_fourConstraint_lower_bound_gt_two
    (q : ℕ) (hq : 1024 ≤ q) :
    (2 : ℝ) < ((q : ℝ) + 1 - 30 * Real.sqrt (q : ℝ)) / 16 := by
  have hqR : (1024 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hs32 : 32 ≤ Real.sqrt (q : ℝ) := by
    by_contra h
    have hslt : Real.sqrt (q : ℝ) < 32 := lt_of_not_ge h
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hs32)
    (show (0 : ℝ) ≤ Real.sqrt (q : ℝ) + 2 by positivity)
  have hmain : (32 : ℝ) < (q : ℝ) + 1 - 30 * Real.sqrt (q : ℝ) := by
    nlinarith
  linarith

/-- If an integer count dominates the Fourier/Hasse lower bound, it contains
    at least three norm-one elements, enough to avoid two exceptional points. -/
theorem k4_normOne_fourConstraint_count_gt_two
    (q N : ℕ) (hq : 1024 ≤ q)
    (hN : ((q : ℝ) + 1 - 30 * Real.sqrt (q : ℝ)) / 16 ≤ (N : ℝ)) :
    2 < N := by
  have h := k4_normOne_fourConstraint_lower_bound_gt_two q hq
  have hN' : (2 : ℝ) < (N : ℝ) := lt_of_lt_of_le h hN
  exact_mod_cast hN'

/-- The five-point exceptional-fiber loss in the current Hasse bridge
    changes the Fourier positivity threshold to q ≥ 2^11. -/
theorem k4_normOne_fourConstraint_lower_bound_gt_two_with_fiber_loss
    (q : ℕ) (hq : 2048 ≤ q) :
    (2 : ℝ) < ((q : ℝ)+1-30*Real.sqrt (q : ℝ)-60)/16 := by
  have hqR : (2048 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q : ℝ))^2=(q : ℝ) := Real.sq_sqrt hq0
  have hs45 : 45 ≤ Real.sqrt (q : ℝ) := by
    by_contra h
    have hslt : Real.sqrt (q : ℝ)<45 := lt_of_not_ge h
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hs45)
    (show (0:ℝ)≤Real.sqrt (q : ℝ)+15 by positivity)
  have hmain : (32:ℝ)<(q : ℝ)+1-30*Real.sqrt (q : ℝ)-60 := by
    nlinarith
  linarith

theorem k4_normOne_fourConstraint_count_gt_two_with_fiber_loss
    (q N : ℕ) (hq : 2048 ≤ q)
    (hN : ((q : ℝ)+1-30*Real.sqrt (q : ℝ)-60)/16 ≤ (N:ℝ)) :
    2<N := by
  have h := k4_normOne_fourConstraint_lower_bound_gt_two_with_fiber_loss q hq
  have hN' : (2:ℝ)<(N:ℝ) := lt_of_lt_of_le h hN
  exact_mod_cast hN'

theorem k4_normOne_fourConstraint_lower_bound_gt_three_with_fiber_loss
    (q : ℕ) (hq : 2048 ≤ q) :
    (3 : ℝ) < ((q : ℝ)+1-30*Real.sqrt (q : ℝ)-60)/16 := by
  have hqR : (2048 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (q : ℝ))^2=(q : ℝ) := Real.sq_sqrt hq0
  have hs45 : 45 ≤ Real.sqrt (q : ℝ) := by
    by_contra h
    have hslt : Real.sqrt (q : ℝ)<45 := lt_of_not_ge h
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hs45)
    (show (0:ℝ)≤Real.sqrt (q : ℝ)+15 by positivity)
  have hmain : (48:ℝ)<(q:ℝ)+1-30*Real.sqrt (q:ℝ)-60 := by
    nlinarith
  linarith

theorem k4_normOne_fourConstraint_count_gt_three_with_fiber_loss
    (q N : ℕ) (hq : 2048 ≤ q)
    (hN : ((q : ℝ)+1-30*Real.sqrt (q : ℝ)-60)/16 ≤ (N:ℝ)) :
    3<N := by
  have h := k4_normOne_fourConstraint_lower_bound_gt_three_with_fiber_loss q hq
  have hN' : (3:ℝ)<(N:ℝ) := lt_of_lt_of_le h hN
  exact_mod_cast hN'

/-- Once the first coefficient is one, the norm-one equation has only the two
    exceptional second coefficients 0 and 1. -/
theorem k4_normOne_exceptions_of_first_eq_one
    {K : Type*} [Field K] [CharP K 2] (a u : K)
    (h : a^2 + a * u + u^2 = 1) (ha : a = 1) : u = 0 ∨ u = 1 := by
  subst a
  have hu : u^2 + u = 0 := by linear_combination h
  have hfac : u * (u + 1) = 0 := by calc
    u * (u + 1) = u^2 + u := by ring
    _ = 0 := hu
  rcases mul_eq_zero.mp hfac with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (by simpa only [CharTwo.neg_eq] using
      (add_eq_zero_iff_eq_neg.mp hone))

theorem k4_normOne_second_eq_one_of_first_eq_zero
    {K : Type*} [Field K] [CharP K 2] (a u : K)
    (h : a^2+a*u+u^2=1) (ha : a=0) : u=1 := by
  subst a
  have hu2 : u^2=1 := by linear_combination h
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have hsq : (u+1)^2=0 := by
    rw [add_sq, hu2]
    simp [h2, CharTwo.add_self_eq_zero]
  have hmul : (u+1)*(u+1)=0 := by simpa only [pow_two] using hsq
  have hu : u+1=0 := by
    rcases mul_eq_zero.mp hmul with h | h <;> exact h
  simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp hu)

#print axioms k4_normOne_fourConstraint_lower_bound_gt_two
#print axioms k4_normOne_fourConstraint_count_gt_two
#print axioms k4_normOne_fourConstraint_lower_bound_gt_two_with_fiber_loss
#print axioms k4_normOne_fourConstraint_count_gt_two_with_fiber_loss
#print axioms k4_normOne_fourConstraint_lower_bound_gt_three_with_fiber_loss
#print axioms k4_normOne_fourConstraint_count_gt_three_with_fiber_loss
#print axioms k4_normOne_exceptions_of_first_eq_one
#print axioms k4_normOne_second_eq_one_of_first_eq_zero

end Carlet
