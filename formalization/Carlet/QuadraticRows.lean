import Carlet.IndexedProduct
import Mathlib.Algebra.Algebra.ZMod

/-!
Bounded triangular-coordinate hypotheses from manuscript Y_r. Total
functions are used only as containers; all conclusions concern indices
strictly below r. This file does not identify the containers with a scheme.
-/

noncomputable section

open Polynomial

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

def TriangularRelations (c : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ) : Prop :=
  (∀ a < r, u a a = 1) ∧
  (∀ a < r, ∀ j < a, u a j ^ 2 + u a j = c j * u a (j+1))

theorem row_eval_scale (c : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) (a : ℕ) (ha : a < r) :
    (reconstructedPolynomial c a).eval (u a 0) = scale c a :=
  reconstructed_diagonal c (u a) a (h.2 a ha) (h.1 a ha)

theorem rows_indexedProduct (h2 : (2 : A) = 0) (c : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) (a : ℕ) (ha : a ≤ r) :
    indexedProduct (fun j => u j 0) a = reconstructedPolynomial c a := by
  apply indexedProduct_eq_reconstructed h2
  intro j hj
  exact row_eval_scale c u r h j (lt_of_lt_of_le hj ha)

theorem rows_fullRank (h2 : (2 : A) = 0) (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j) :
    ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination (fun j => u j 0) r b) := by
  apply all_nonzero_combinations_isUnit
  intro j hj
  rw [rows_indexedProduct h2 c u r h j (Nat.le_of_lt hj), row_eval_scale c u r h j hj]
  apply reconstructed_scale_isUnit c t d j
  · intro k hk
    exact ht k (lt_of_le_of_lt hk hj)
  · intro k hk
    exact hc k (by omega)

theorem rows_normalized (c : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) (hr : 0 < r) : u 0 0 = 1 :=
  h.1 0 hr

theorem rows_recover_all_coordinates (c : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) (a j : ℕ) (ha : a < r) (hj : j ≤ a)
    (d : A) (hd : scale c j * d = 1) :
    (reconstructedPolynomial c j).eval (u a 0) * d = u a j := by
  apply recover_coordinate
  · intro k hk
    exact h.2 a ha k (lt_of_lt_of_le hk hj)
  · exact hd

/-- Every F₂-algebra has 2=0, including the zero ring. -/
theorem algebra_two_eq_zero [Algebra (ZMod 2) A] : (2 : A) = 0 := by
  have h := congrArg (algebraMap (ZMod 2) A) (show (2 : ZMod 2) = 0 by decide)
  simpa only [map_ofNat, map_zero] using h

theorem rows_fullRank_of_algebra [Algebra (ZMod 2) A]
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r)
    (ht : ∀ j < r, t j * d j = 1)
    (hc : ∀ j, j+1 < r → c j * t (j+1) = t j) :
    ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination (fun j => u j 0) r b) :=
  rows_fullRank algebra_two_eq_zero c t d u r h ht hc

#print axioms rows_indexedProduct
#print axioms rows_fullRank_of_algebra
#print axioms rows_recover_all_coordinates

end Carlet.Quadratic
