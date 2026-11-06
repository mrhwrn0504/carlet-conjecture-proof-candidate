import Mathlib.Tactic

namespace Carlet

theorem combined_four_residual_minimum (n : ℕ) (hn : Odd n) (hbound : 9 ≤ n)
    (h7 : ¬ 7 ∣ n) (h9 : ¬ 9 ∣ n) (h11 : ¬ 11 ∣ n) (h13 : ¬ 13 ∣ n)
    (h15 : ¬ 15 ∣ n) (h17 : ¬ 17 ∣ n) (h19 : ¬ 19 ∣ n) : 23 ≤ n := by
  by_contra h
  have hlt : n < 23 := by omega
  interval_cases n <;> norm_num at *

theorem combined_five_residual_minimum (n : ℕ) (hn : Odd n) (hbound : 11 ≤ n)
    (h5 : ¬ 5 ∣ n) (h9 : ¬ 9 ∣ n) (h11 : ¬ 11 ∣ n) (h13 : ¬ 13 ∣ n)
    (h17 : ¬ 17 ∣ n) (h19 : ¬ 19 ∣ n) (h21 : ¬ 21 ∣ n) (h23 : ¬ 23 ∣ n)
    (h29 : ¬ 29 ∣ n) (h31 : ¬ 31 ∣ n) : 37 ≤ n := by
  by_contra h
  have hlt : n < 37 := by omega
  interval_cases n <;> norm_num at *

theorem combined_four_residual_23 :
    Odd 23 ∧ 9 ≤ 23 ∧ ¬ 7 ∣ 23 ∧ ¬ 9 ∣ 23 ∧ ¬ 11 ∣ 23 ∧ ¬ 13 ∣ 23 ∧
      ¬ 15 ∣ 23 ∧ ¬ 17 ∣ 23 ∧ ¬ 19 ∣ 23 := by norm_num

theorem combined_five_residual_37 :
    Odd 37 ∧ 11 ≤ 37 ∧ ¬ 5 ∣ 37 ∧ ¬ 9 ∣ 37 ∧ ¬ 11 ∣ 37 ∧ ¬ 13 ∣ 37 ∧
      ¬ 17 ∣ 37 ∧ ¬ 19 ∣ 37 ∧ ¬ 21 ∣ 37 ∧ ¬ 23 ∣ 37 ∧ ¬ 29 ∣ 37 ∧
      ¬ 31 ∣ 37 := by norm_num

#print axioms combined_four_residual_minimum
#print axioms combined_five_residual_minimum
#print axioms combined_four_residual_23
#print axioms combined_five_residual_37
end Carlet
