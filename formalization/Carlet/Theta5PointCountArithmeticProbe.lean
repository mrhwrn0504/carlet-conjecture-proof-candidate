import Mathlib.Tactic

namespace Carlet

/-- Coarse integer core of the k=5 point-count inequality for odd
    `n = 2*m+1 >= 21`. The geometric estimate still has to supply this
    bracket; this lemma only closes its final arithmetic step. -/
theorem theta5_coarse_point_count_bracket_pos (m : ℕ) (hm : 10 ≤ m) :
    (2 : ℝ) ^ (2 * m + 1) - 210 * (2 : ℝ) ^ (m + 1) -
      (5 * (2 : ℝ) ^ 18 + 31 ^ 2) > 0 := by
  let x : ℝ := (2 : ℝ) ^ m
  have hx : (1024 : ℝ) ≤ x := by
    dsimp [x]
    have hn : 2 ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    exact_mod_cast hn
  have hsmall : (2 : ℝ) ^ (m + 1) = 2 * x := by
    rw [pow_succ]
    dsimp [x]
    ring
  have hlarge : (2 : ℝ) ^ (2 * m + 1) = 2 * x ^ 2 := by
    have he : 2 * m + 1 = (m + 1) + m := by omega
    rw [he, pow_add, hsmall]
    dsimp [x]
    ring
  have hinc : 0 ≤ (x - 1024) * (2 * (x + 1024) - 420) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hlarge, hsmall]
  norm_num
  nlinarith [hinc]

#print axioms theta5_coarse_point_count_bracket_pos

end Carlet
