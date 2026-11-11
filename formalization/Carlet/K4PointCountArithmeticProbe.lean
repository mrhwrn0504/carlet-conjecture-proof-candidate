import Carlet.K4RootBoundProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet

theorem k4_explicit_point_bound_implies_large_count (q N : ℕ) (hq : 131072 ≤ q)
    (hbound : (q : ℝ)^3 - 48 * Real.sqrt (q : ℝ) * (q : ℝ)^2 -
      40960 * (q : ℝ)^2 ≤ (N : ℝ)) : 120*q^2 < N := by
  have hqr : (131072 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqp : (0 : ℝ) < (q : ℝ) := by linarith
  have hm := k4_theta4_lang_weil_numeric_margin (q : ℝ) hqr
  have hmul := mul_pos (sq_pos_of_pos hqp) hm
  have hgt : (120 : ℝ)*(q : ℝ)^2 < (N : ℝ) := by nlinarith
  exact_mod_cast hgt

#print axioms k4_explicit_point_bound_implies_large_count
end Carlet
