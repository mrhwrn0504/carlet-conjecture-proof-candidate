import Carlet.K4ResidualArithmetic23Probe
import Mathlib.Tactic
namespace Carlet

theorem k4_remaining_lower_bound_after_25 (n : ℕ) (hn : Odd n) (hbound : 7 ≤ n)
    (h7 : ¬ 7 ∣ n) (h9 : ¬ 9 ∣ n) (h11 : ¬ 11 ∣ n) (h13 : ¬ 13 ∣ n)
    (h15 : ¬ 15 ∣ n) (h17 : ¬ 17 ∣ n) (h19 : ¬ 19 ∣ n) (h23 : ¬ 23 ∣ n)
    (h25 : ¬ 25 ∣ n) : 29 ≤ n := by
  have hmin := k4_remaining_lower_bound_after_23 n hn hbound h7 h9 h11 h13 h15 h17 h19 h23
  by_contra h
  have hmax : n ≤ 28 := by omega
  interval_cases n <;> norm_num at *

theorem k4_remaining_29 : Odd 29 ∧ 7 ≤ 29 ∧
    ¬ 7 ∣ 29 ∧ ¬ 9 ∣ 29 ∧ ¬ 11 ∣ 29 ∧ ¬ 13 ∣ 29 ∧ ¬ 15 ∣ 29 ∧
    ¬ 17 ∣ 29 ∧ ¬ 19 ∣ 29 ∧ ¬ 23 ∣ 29 ∧ ¬ 25 ∣ 29 := by norm_num

#print axioms k4_remaining_lower_bound_after_25
#print axioms k4_remaining_29
end Carlet
