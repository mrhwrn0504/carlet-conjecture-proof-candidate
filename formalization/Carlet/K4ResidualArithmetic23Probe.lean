import Mathlib.Tactic

namespace Carlet

theorem k4_remaining_lower_bound_after_23 (n : ℕ) (hn : Odd n) (hbound : 7 ≤ n)
    (h7 : ¬ 7 ∣ n) (h9 : ¬ 9 ∣ n) (h11 : ¬ 11 ∣ n) (h13 : ¬ 13 ∣ n)
    (h15 : ¬ 15 ∣ n) (h17 : ¬ 17 ∣ n) (h19 : ¬ 19 ∣ n) (h23 : ¬ 23 ∣ n) :
    25 ≤ n := by
  by_contra h
  have hn24 : n ≤ 24 := by omega
  interval_cases n <;> norm_num at *

theorem k4_remaining_25 : Odd 25 ∧ 7 ≤ 25 ∧
    ¬ 7 ∣ 25 ∧ ¬ 9 ∣ 25 ∧ ¬ 11 ∣ 25 ∧ ¬ 13 ∣ 25 ∧ ¬ 15 ∣ 25 ∧
    ¬ 17 ∣ 25 ∧ ¬ 19 ∣ 25 ∧ ¬ 23 ∣ 25 := by norm_num

#print axioms k4_remaining_lower_bound_after_23
#print axioms k4_remaining_25
end Carlet
