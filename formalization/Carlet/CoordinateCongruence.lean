import Carlet.CoordinateRoundTrip

noncomputable section

open scoped BigOperators

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

theorem combination_congr (x y : ℕ → A) (r : ℕ) (h : ∀ j < r, x j = y j)
    (b : Bits r) : combination x r b = combination y r b := by
  induction r with
  | zero => rfl
  | succ n ih =>
    change combination x n b.1 + (if b.2 then x n else 0) =
      combination y n b.1 + (if b.2 then y n else 0)
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)) b.1, h n (Nat.lt_succ_self n)]

theorem openCarletCondition_transfer (x y : ℕ → A) (r : ℕ) (hr : 0 < r)
    (hxy : ∀ j < r, x j = y j) (h : OpenCarletCondition x r) :
    OpenCarletCondition y r := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← hxy 0 hr]
    exact h.1
  · intro b hb
    rw [← combination_congr x y r hxy b]
    exact h.2.1 b hb
  · change (∑ b : Bits r, Ring.inverse (combination y r b)) = 0
    calc
      _ = fullReciprocalSum x r := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [combination_congr x y r hxy b]
      _ = 0 := h.2.2

theorem quadraticCondition_transfer (c t d c' t' d' : ℕ → A)
    (u u' : ℕ → ℕ → A) (r : ℕ) (hr : 0 < r)
    (hec : ∀ j, j+1 < r → c j = c' j)
    (het : ∀ j < r, t j = t' j) (hed : ∀ j < r, d j = d' j)
    (heu : ∀ a < r, ∀ j ≤ a, u a j = u' a j)
    (h : QuadraticCondition c t d u r) : QuadraticCondition c' t' d' u' r := by
  obtain ⟨hu, ht0, htd, hct, hsum⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [← heu a ha a (Nat.le_refl a)]
    exact hu.1 a ha
  · intro a ha j hj
    rw [← heu a ha j (Nat.le_of_lt hj), ← heu a ha (j+1) (by omega),
      ← hec j (by omega)]
    exact hu.2 a ha j hj
  · rw [← het 0 hr]
    exact ht0
  · intro j hj
    rw [← het j hj, ← hed j hj]
    exact htd j hj
  · intro j hj
    rw [← hec j hj, ← het (j+1) hj, ← het j (by omega)]
    exact hct j hj
  · calc
      _ = ∑ j ∈ Finset.range r, t j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (het j (Finset.mem_range.mp hj)).symm
      _ = 0 := hsum

#print axioms openCarletCondition_transfer
#print axioms quadraticCondition_transfer

end Carlet.Quadratic
