import Carlet.BaseChange

noncomputable section

open scoped BigOperators

namespace Carlet.Quadratic

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The explicit normalized open Carlet equations, represented by a total
coordinate sequence but using only its first r entries. -/
def OpenCarletCondition (x : ℕ → A) (r : ℕ) : Prop :=
  x 0 = 1 ∧
  (∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination x r b)) ∧
  fullReciprocalSum x r = 0

/-- Reverse direction of the bounded coordinate construction: all three
actual open-Carlet conditions follow from the quadratic equations. -/
theorem reverse_satisfies_openCarlet [Algebra (ZMod 2) A]
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ) (hr : 0 < r)
    (h : TriangularRelations c u r) (ht0 : t 0 = 1)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j)
    (hsum : (∑ j ∈ Finset.range r, t j) = 0) :
    OpenCarletCondition (fun j => u j 0) r := by
  exact ⟨rows_normalized c u r h hr,
    rows_fullRank_of_algebra c t d u r h ht hc,
    rows_zeroSum algebra_two_eq_zero c t d u r h ht0 ht hc hsum⟩

theorem openCarletCondition_map (f : A →+* B) (x : ℕ → A) (r : ℕ)
    (h : OpenCarletCondition x r) : OpenCarletCondition (f ∘ x) r := by
  refine ⟨?_, fullRank_map f x r h.2.1, ?_⟩
  · change f (x 0) = 1
    rw [h.1, map_one]
  · rw [← fullReciprocalSum_map f x r h.2.1, h.2.2, map_zero]

#print axioms reverse_satisfies_openCarlet
#print axioms openCarletCondition_map

end Carlet.Quadratic
