import Carlet.ReciprocalBlocks

noncomputable section

open Polynomial
open scoped BigOperators Ring

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

def reciprocalRatio (c : ℕ → A) (n : ℕ) : A :=
  linearScale c n * Ring.inverse (scale c n)

theorem bounded_scale_isUnit (c t d : ℕ → A) (r n : ℕ) (hn : n < r)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j) : IsUnit (scale c n) := by
  apply reconstructed_scale_isUnit c t d n
  · intro j hj
    exact ht j (lt_of_le_of_lt hj hn)
  · intro j hj
    exact hc j (by omega)

theorem reciprocalRatio_step (c : ℕ → A) (n : ℕ)
    (hn : IsUnit (scale c n)) (hn1 : IsUnit (scale c (n+1))) :
    c n * reciprocalRatio c (n+1) = reciprocalRatio c n := by
  have hd := Ring.mul_inverse_cancel (scale c n) hn
  have hd1 := Ring.mul_inverse_cancel (scale c (n+1)) hn1
  apply hn1.mul_left_cancel
  change scale c (n+1) * (c n * (scale c n * linearScale c n * Ring.inverse (scale c (n+1)))) =
    scale c (n+1) * (linearScale c n * Ring.inverse (scale c n))
  calc
    _ = (c n * scale c n * linearScale c n) *
          (scale c (n+1) * Ring.inverse (scale c (n+1))) := by ring
    _ = c n * scale c n * linearScale c n := by rw [hd1, mul_one]
    _ = (c n * scale c n * linearScale c n) *
          (scale c n * Ring.inverse (scale c n)) := by rw [hd, mul_one]
    _ = (c n * scale c n ^ 2) * (linearScale c n * Ring.inverse (scale c n)) := by ring
    _ = _ := rfl

theorem reciprocalRatio_eq_t (c t d : ℕ → A) (r : ℕ) (ht0 : t 0 = 1)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j) :
    ∀ n < r, reciprocalRatio c n = t n := by
  intro n
  induction n with
  | zero => intro hn; simp [reciprocalRatio, linearScale, scale, ht0]
  | succ n ih =>
    intro hn
    have hn0 : n < r := by omega
    have hcu : IsUnit (c n) := ratio_isUnit _ _ _ (hc n hn)
      (coordinate_isUnit _ _ (ht n hn0))
    apply hcu.mul_left_cancel
    rw [hc n hn]
    rw [reciprocalRatio_step c n (bounded_scale_isUnit c t d r n hn0 ht hc)
      (bounded_scale_isUnit c t d r (n+1) hn ht hc), ih hn0]

theorem rows_blockSum_eq_t (h2 : (2 : A) = 0)
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) (ht0 : t 0 = 1)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j) (n : ℕ) (hn : n < r) :
    blockSum (fun j => u j 0) n = t n := by
  have hunit : IsUnit ((indexedProduct (fun j => u j 0) n).eval (u n 0)) := by
    rw [rows_indexedProduct h2 c u r h n (Nat.le_of_lt hn), row_eval_scale c u r h n hn]
    exact bounded_scale_isUnit c t d r n hn ht hc
  rw [blockSum_eq_scale_ratio h2 (fun j => u j 0) c n
    (fun j hj => row_eval_scale c u r h j (lt_of_le_of_lt hj hn))
    (fun b => by simpa only [add_comm] using
      translated_combination_isUnit (fun j => u j 0) n hunit b)]
  exact reciprocalRatio_eq_t c t d r ht0 ht hc n hn

def fullReciprocalSum (x : ℕ → A) (n : ℕ) : A :=
  ∑ b : Bits n, Ring.inverse (combination x n b)

theorem fullReciprocalSum_eq_nonzero (x : ℕ → A) (r : ℕ) [DecidableEq (Bits r)] :
    fullReciprocalSum x r =
      ∑ b ∈ (Finset.univ : Finset (Bits r)).erase (zeroBits r),
        Ring.inverse (combination x r b) := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Bits r))
    (fun b => Ring.inverse (combination x r b)) (Finset.mem_univ (zeroBits r))
  simpa only [combination_zeroBits, Ring.inverse_zero, add_zero, fullReciprocalSum] using h.symm

theorem fullReciprocalSum_step (x : ℕ → A) (n : ℕ) :
    fullReciprocalSum x (n+1) = fullReciprocalSum x n + blockSum x n := by
  change (∑ b : Bits n × Bool,
    Ring.inverse (combination x n b.1 + if b.2 then x n else 0)) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false, add_zero]
  rw [Finset.sum_add_distrib]
  simp only [fullReciprocalSum, blockSum]
  simp only [add_comm]

theorem fullReciprocalSum_eq_blocks (x : ℕ → A) (r : ℕ) :
    fullReciprocalSum x r = ∑ j ∈ Finset.range r, blockSum x j := by
  induction r with
  | zero => simp [fullReciprocalSum, combination, Ring.inverse_zero]
  | succ n ih => rw [fullReciprocalSum_step, ih, Finset.sum_range_succ]

/-- The reverse triangular construction satisfies the actual reciprocal
sum equation, not merely the auxiliary relation on t coordinates. -/
theorem rows_zeroSum (h2 : (2 : A) = 0)
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) (ht0 : t 0 = 1)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j)
    (hsum : (∑ j ∈ Finset.range r, t j) = 0) :
    fullReciprocalSum (fun j => u j 0) r = 0 := by
  rw [fullReciprocalSum_eq_blocks]
  calc
    _ = ∑ j ∈ Finset.range r, t j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact rows_blockSum_eq_t h2 c t d u r h ht0 ht hc j (Finset.mem_range.mp hj)
    _ = 0 := hsum

#print axioms reciprocalRatio_eq_t
#print axioms rows_blockSum_eq_t
#print axioms rows_zeroSum
#print axioms fullReciprocalSum_eq_nonzero

end Carlet.Quadratic
