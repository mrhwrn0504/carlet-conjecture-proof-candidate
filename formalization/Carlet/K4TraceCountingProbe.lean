import Mathlib.Tactic

noncomputable section
open scoped BigOperators

/-- Seven lower bounds imply a common +1 value for three sign functions. -/
theorem triple_sign_exists_of_sum_bounds {A : Type*} (S : Finset A)
    (a b c : A → ℝ) (B : ℝ)
    (ha : ∀ x ∈ S, a x = 1 ∨ a x = -1)
    (hb : ∀ x ∈ S, b x = 1 ∨ b x = -1)
    (hc : ∀ x ∈ S, c x = 1 ∨ c x = -1)
    (h1 : -B ≤ ∑ x ∈ S, a x) (h2 : -B ≤ ∑ x ∈ S, b x)
    (h3 : -B ≤ ∑ x ∈ S, c x) (h12 : -B ≤ ∑ x ∈ S, a x*b x)
    (h13 : -B ≤ ∑ x ∈ S, a x*c x) (h23 : -B ≤ ∑ x ∈ S, b x*c x)
    (h123 : -B ≤ ∑ x ∈ S, a x*b x*c x)
    (hsize : 7*B < (S.card : ℝ)) :
    ∃ x ∈ S, a x = 1 ∧ b x = 1 ∧ c x = 1 := by
  classical
  by_contra hnone
  have hz : ∀ x ∈ S, (1+a x)*(1+b x)*(1+c x) = 0 := by
    intro x hx
    have hnot : ¬ (a x = 1 ∧ b x = 1 ∧ c x = 1) := by
      intro h
      exact hnone ⟨x, hx, h⟩
    rcases ha x hx with ha' | ha' <;>
      rcases hb x hx with hb' | hb' <;>
      rcases hc x hx with hc' | hc' <;> simp_all
  have hsum : (∑ x ∈ S, (1+a x)*(1+b x)*(1+c x)) = 0 := by
    exact Finset.sum_eq_zero hz
  have hexpand : (∑ x ∈ S, (1+a x)*(1+b x)*(1+c x)) =
      (S.card : ℝ) + (∑ x ∈ S, a x) + (∑ x ∈ S, b x) + (∑ x ∈ S, c x) +
      (∑ x ∈ S, a x*b x) + (∑ x ∈ S, a x*c x) +
      (∑ x ∈ S, b x*c x) + (∑ x ∈ S, a x*b x*c x) := by
    calc
      _ = ∑ x ∈ S, (1 + a x + b x + c x + a x*b x + a x*c x + b x*c x + a x*b x*c x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

/-- The conservative genus-five bound is positive from q=2^13 onward. -/
theorem k4_genus_five_numeric_margin (q : ℝ) (hq : 8192 ≤ q) :
    0 < q - 70*Real.sqrt q - 13 := by
  have hs := Real.sqrt_nonneg q
  have hsq := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hs90 : 90 < Real.sqrt q := by nlinarith
  have hp : 0 < (Real.sqrt q - 90)*(Real.sqrt q - 70) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

#print axioms triple_sign_exists_of_sum_bounds
#print axioms k4_genus_five_numeric_margin
