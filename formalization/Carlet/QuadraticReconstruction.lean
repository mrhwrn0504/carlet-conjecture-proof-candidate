import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Tactic.Ring

/-!
Arbitrary-ring algebra behind the reverse direction of manuscript Theorem 4.2.
Index n corresponds to manuscript j=n+1: delta(0)=delta_1=1,
and P(n)=L_n. This does not yet assert the full scheme isomorphism.
No field, reducedness, domain, or nontriviality assumption is made.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

def scale (c : ℕ → A) : ℕ → A
  | 0 => 1
  | n+1 => c n * scale c n ^ 2

def reconstructedPolynomial (c : ℕ → A) : ℕ → A[X]
  | 0 => X
  | n+1 => reconstructedPolynomial c n ^ 2 + C (scale c n) * reconstructedPolynomial c n

/-- The arbitrary-base reconstruction identity (4.8), with explicit
finite bounds on the required Artin–Schreier relations. -/
theorem reconstructed_eval (c u : ℕ → A) (n : ℕ)
    (h : ∀ j < n, u j ^ 2 + u j = c j * u (j+1)) :
    (reconstructedPolynomial c n).eval (u 0) = scale c n * u n := by
  induction n with
  | zero => simp [reconstructedPolynomial, scale]
  | succ n ih =>
    have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hn := h n (Nat.lt_succ_self n)
    simp only [reconstructedPolynomial, eval_add, eval_pow, eval_mul, eval_C, hi, scale]
    calc
      (scale c n * u n) ^ 2 + scale c n * (scale c n * u n) =
          scale c n ^ 2 * (u n ^ 2 + u n) := by ring
      _ = c n * scale c n ^ 2 * u (n+1) := by rw [hn]; ring

theorem reconstructed_diagonal (c u : ℕ → A) (n : ℕ)
    (h : ∀ j < n, u j ^ 2 + u j = c j * u (j+1)) (hu : u n = 1) :
    (reconstructedPolynomial c n).eval (u 0) = scale c n := by
  rw [reconstructed_eval c u n h, hu, mul_one]

theorem scale_isUnit (c : ℕ → A) (n : ℕ) (h : ∀ j < n, IsUnit (c j)) :
    IsUnit (scale c n) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih =>
    exact (h n (Nat.lt_succ_self n)).mul
      ((ih (fun j hj => h j (Nat.lt_succ_of_lt hj))).pow 2)

theorem coordinate_isUnit (t d : A) (h : t * d = 1) : IsUnit t := by
  exact ⟨⟨t, d, h, by simpa only [mul_comm] using h⟩, rfl⟩

theorem ratio_isUnit (c tNext tPrev : A) (h : c * tNext = tPrev)
    (ht : IsUnit tPrev) : IsUnit c := by
  have hp : IsUnit (c * tNext) := h.symm ▸ ht
  exact isUnit_of_mul_isUnit_left hp

theorem reconstructed_scale_isUnit (c t d : ℕ → A) (n : ℕ)
    (ht : ∀ j ≤ n, t j * d j = 1)
    (hc : ∀ j < n, c j * t (j+1) = t j) : IsUnit (scale c n) := by
  apply scale_isUnit
  intro j hj
  exact ratio_isUnit _ _ _ (hc j hj) (coordinate_isUnit _ _ (ht j (Nat.le_of_lt hj)))

/-- A product being a unit forces each of its finitely many factors to
be a unit, even in a nonreduced or zero ring. -/
theorem factor_isUnit {ι : Type*} (s : Finset ι) (f : ι → A)
    (h : IsUnit (∏ j ∈ s, f j)) (i : ι) (hi : i ∈ s) : IsUnit (f i) := by
  classical
  rw [← Finset.mul_prod_erase s f hi] at h
  exact isUnit_of_mul_isUnit_left h

/-- Recover one original u coordinate after reverse reconstruction and
forward division, with division expressed by an explicit inverse. -/
theorem recover_coordinate (c u : ℕ → A) (n : ℕ) (d : A)
    (h : ∀ j < n, u j ^ 2 + u j = c j * u (j+1))
    (hd : scale c n * d = 1) :
    (reconstructedPolynomial c n).eval (u 0) * d = u n := by
  rw [reconstructed_eval c u n h]
  calc
    (scale c n * u n) * d = u n * (scale c n * d) := by ring
    _ = u n := by rw [hd, mul_one]

#print axioms reconstructed_eval
#print axioms reconstructed_diagonal
#print axioms reconstructed_scale_isUnit
#print axioms factor_isUnit
#print axioms recover_coordinate

end Carlet.Quadratic
