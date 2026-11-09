import Mathlib

/-!
# Carlet v7: direct elimination of the final reciprocal coordinate

The only eliminated coordinate is t_r.  No auxiliary s_i or v_{a,j}
coordinates are introduced.

Crucially, the original t-coordinates are a function on Fin r (t₁,…,t_r),
whereas the v7 coordinates are a function on Fin (r-1) (t₁,…,t_{r-1}).
Thus t_r is removed from the coordinate type itself, not merely omitted
from a list of equations.
-/

open scoped BigOperators

namespace Carlet.QuadraticV7

variable {A : Type*} [CommRing A]

/-- The retained contribution t₂ + ⋯ + t_{r-1}. -/
def prefixSum (t : Fin (r - 1) → A) (r : ℕ) : A :=
  ∑ i ∈ Finset.range (r - 2), t ⟨i + 1, by omega⟩

/-- The same prefix, viewed in the original coordinate space. -/
def prefixSumOriginal (t : Fin r → A) (r : ℕ) : A :=
  ∑ i ∈ Finset.range (r - 2), t ⟨i + 1, by omega⟩

/-- The original contribution t₂ + ⋯ + t_r. -/
def totalSum (t : Fin r → A) (r : ℕ) : A :=
  ∑ i ∈ Finset.range (r - 1), t ⟨i + 1, by omega⟩

/-- The last original coordinate t_r. -/
def lastCoordinate (t : Fin r → A) (r : ℕ) : A :=
  t ⟨r - 1, by omega⟩

/-- Restrict the original coordinates to t₁,…,t_{r-1}. -/
def truncate (t : Fin r → A) (r : ℕ) : Fin (r - 1) → A :=
  fun i => t ⟨i.val, by omega⟩

/-- Splitting off t_r from the original finite sum. -/
theorem totalSum_eq_prefix_add_last (t : Fin r → A) (r : ℕ)
    (hr : 2 ≤ r) :
    totalSum t r = prefixSumOriginal t r + lastCoordinate t r := by
  unfold totalSum prefixSumOriginal lastCoordinate
  rw [show r - 1 = (r - 2) + 1 by omega, Finset.sum_range_succ]
  congr 1
  apply congrArg t
  apply Fin.ext
  simp
  omega

/-- Restricting to the first r-1 coordinates preserves the prefix sum. -/
theorem prefixSum_truncate (t : Fin r → A) (r : ℕ) (hr : 2 ≤ r) :
    prefixSum (truncate t r) r = prefixSumOriginal t r := by
  unfold prefixSum prefixSumOriginal truncate
  refine Finset.sum_congr rfl ?_
  intro i hi
  rfl

/-- In characteristic two, every element is its own additive inverse. -/
theorem add_self_eq_zero_of_two_eq_zero (h₂ : (2 : A) = 0) (x : A) :
    x + x = 0 := by
  calc
    x + x = (2 : A) * x := by ring
    _ = 0 := by rw [h₂]; simp

/--
The final zero-sum equation uniquely determines the deleted coordinate:
t_r = 1 + t₂ + ⋯ + t_{r-1}.
-/
theorem last_sum_iff_last_coordinate (t : Fin r → A) (r : ℕ)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0) :
    1 + totalSum t r = 0 ↔
      lastCoordinate t r = 1 + prefixSumOriginal t r := by
  rw [totalSum_eq_prefix_add_last t r hr]
  constructor
  · intro h
    have hx := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSumOriginal t r)
    have hsum : lastCoordinate t r + (1 + prefixSumOriginal t r) = 0 := by
      simpa [add_assoc, add_comm, add_left_comm] using h
    calc
      lastCoordinate t r =
          lastCoordinate t r + 0 := by simp
      _ = lastCoordinate t r +
          ((1 + prefixSumOriginal t r) +
            (1 + prefixSumOriginal t r)) := by rw [hx]; simp
      _ = (lastCoordinate t r +
            (1 + prefixSumOriginal t r)) +
            (1 + prefixSumOriginal t r) := by ac_rfl
      _ = 0 + (1 + prefixSumOriginal t r) := by rw [hsum]
      _ = 1 + prefixSumOriginal t r := by simp
  · intro hlast
    have hx := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSumOriginal t r)
    calc
      1 + (prefixSumOriginal t r + lastCoordinate t r) =
          (1 + prefixSumOriginal t r) +
            (1 + prefixSumOriginal t r) := by rw [hlast]; ac_rfl
      _ = 0 := hx

/-- Reinsert the deleted coordinate using its forced polynomial expression. -/
def reinsertLast (t : Fin (r - 1) → A) (r : ℕ)
    (hr : 2 ≤ r) : Fin r → A :=
  fun i =>
    if hi : i.val = r - 1 then
      1 + prefixSum t r
    else
      t ⟨i.val, by omega⟩

/-- The reinserted point has exactly the retained prefix sum. -/
theorem prefixSum_reinsertLast (t : Fin (r - 1) → A) (r : ℕ)
    (hr : 2 ≤ r) :
    prefixSumOriginal (reinsertLast t r hr) r = prefixSum t r := by
  unfold prefixSumOriginal prefixSum reinsertLast
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < r - 2 := Finset.mem_range.mp hi
  have hne : i + 1 ≠ r - 1 := by omega
  simp [hne]

/-- The original total sum after reinsertion is prefix plus the forced last term. -/
theorem totalSum_reinsertLast (t : Fin (r - 1) → A) (r : ℕ)
    (hr : 2 ≤ r) :
    totalSum (reinsertLast t r hr) r =
      prefixSum t r + (1 + prefixSum t r) := by
  rw [totalSum_eq_prefix_add_last (reinsertLast t r hr) r hr]
  rw [prefixSum_reinsertLast t r hr]
  simp [lastCoordinate, reinsertLast]

/-- Truncating after reinsertion recovers every retained coordinate. -/
theorem truncate_reinsertLast (t : Fin (r - 1) → A) (r : ℕ)
    (hr : 2 ≤ r) :
    truncate (reinsertLast t r hr) r = t := by
  funext i
  have hne : i.val ≠ r - 1 := by omega
  simp [truncate, reinsertLast, hne]

/-- Truncating an original point and reinserting it changes only its last coordinate. -/
theorem reinsert_truncate_of_original_sum (t : Fin r → A) (r : ℕ)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (hsum : 1 + totalSum t r = 0) :
    reinsertLast (truncate t r) r hr = t := by
  have hlast := (last_sum_iff_last_coordinate t r hr h₂).mp hsum
  have hprefix := prefixSum_truncate t r hr
  funext i
  by_cases hi : i.val = r - 1
  · have hiEq : i = ⟨r - 1, by omega⟩ := Fin.ext hi
    subst i
    change 1 + prefixSum (truncate t r) r = lastCoordinate t r
    rw [hprefix]
    exact hlast.symm
  · simp [reinsertLast, hi, truncate]

/-- The triangular Artin–Schreier equations; the diagonal is fixed to one. -/
def TriangularRelations (u : ℕ → ℕ → A) (c : ℕ → A) (r : ℕ) : Prop :=
  (∀ a, 2 ≤ a → a ≤ r → u a a = 1) ∧
  (∀ a, 2 ≤ a → a ≤ r → ∀ j, 1 ≤ j → j < a →
    u a j ^ 2 + u a j = c j * u a (j + 1))

/-- Original system, with t₁,…,t_r as its actual finite coordinate vector. -/
def OriginalSystem (u : ℕ → ℕ → A) (t : Fin r → A)
    (c : ℕ → A) (r : ℕ) : Prop :=
  TriangularRelations u c r ∧
  (∀ j : Fin (r - 1),
    c (j.val + 1) * t ⟨j.val + 1, by omega⟩ =
      t ⟨j.val, by omega⟩) ∧
  t ⟨0, by omega⟩ = 1 ∧
  1 + totalSum t r = 0

/-- v7 system, whose t-coordinate vector has length r-1, not r. -/
def EliminatedSystem (u : ℕ → ℕ → A) (t : Fin (r - 1) → A)
    (c : ℕ → A) (r : ℕ) : Prop :=
  TriangularRelations u c r ∧
  (∀ j : Fin (r - 2),
    c (j.val + 1) * t ⟨j.val + 1, by omega⟩ =
      t ⟨j.val, by omega⟩) ∧
  t ⟨0, by omega⟩ = 1 ∧
  c (r - 1) * (1 + prefixSum t r) =
    t ⟨r - 2, by omega⟩

/--
Every original solution restricts to a v7 solution.  The final ratio equation
is obtained by substituting the uniquely forced value of t_r.
-/
theorem original_implies_eliminated (u : ℕ → ℕ → A)
    (t : Fin r → A) (c : ℕ → A) (r : ℕ)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (h : OriginalSystem u t c r) :
    EliminatedSystem u (truncate t r) c r := by
  rcases h with ⟨hu, hratio, ht₁, hsum⟩
  have hlastValue := (last_sum_iff_last_coordinate t r hr h₂).mp hsum
  have hlastRatio :
      c (r - 1) * lastCoordinate t r =
        t ⟨r - 2, by omega⟩ := by
    have h := hratio ⟨r - 2, by omega⟩
    simpa [lastCoordinate, show r - 2 + 1 = r - 1 by omega] using h
  refine ⟨hu, ?_, ?_, ?_⟩
  · intro j
    have h := hratio ⟨j.val, by omega⟩
    simpa [truncate] using h
  · simpa [truncate] using ht₁
  · calc
      c (r - 1) * (1 + prefixSum (truncate t r) r) =
          c (r - 1) * lastCoordinate t r := by
            rw [prefixSum_truncate t r hr, ← hlastValue]
      _ = t ⟨r - 2, by omega⟩ := hlastRatio
      _ = truncate t r ⟨r - 2, by omega⟩ := by rfl

/--
Every v7 solution extends uniquely to the original system by restoring the
deleted coordinate as 1 + t₂ + ⋯ + t_{r-1}.
-/
theorem eliminated_implies_original (u : ℕ → ℕ → A)
    (t : Fin (r - 1) → A) (c : ℕ → A) (r : ℕ)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (h : EliminatedSystem u t c r) :
    OriginalSystem u (reinsertLast t r hr) c r := by
  rcases h with ⟨hu, hratio, ht₁, hlast⟩
  refine ⟨hu, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val = r - 2
    · have hjEq : j = ⟨r - 2, by omega⟩ := Fin.ext hj
      subst j
      simpa [reinsertLast, show r - 2 + 1 = r - 1 by omega] using hlast
    · have hjlt : j.val < r - 2 := by omega
      have h := hratio ⟨j.val, hjlt⟩
      have hne₀ : j.val ≠ r - 1 := by omega
      have hne₁ : j.val + 1 ≠ r - 1 := by omega
      simpa [reinsertLast, hne₀, hne₁] using h
  · have hne : 0 ≠ r - 1 := by omega
    simpa [reinsertLast, hne] using ht₁
  · calc
      1 + totalSum (reinsertLast t r hr) r =
          1 + (prefixSum t r + (1 + prefixSum t r)) := by
            rw [totalSum_reinsertLast t r hr]
      _ = 0 := by
        have hx := add_self_eq_zero_of_two_eq_zero (A := A) h₂
          (1 + prefixSum t r)
        calc
          1 + (prefixSum t r + (1 + prefixSum t r)) =
              (1 + prefixSum t r) + (1 + prefixSum t r) := by ac_rfl
          _ = 0 := hx

/-- The boundary r=2 has no retained prefix coordinates. -/
theorem boundary_r2 (t : Fin 1 → A) (c : ℕ → A)
    (ht₁ : t ⟨0, by omega⟩ = 1) :
    c 1 * (1 + prefixSum t 2) = t ⟨0, by omega⟩ ↔ c 1 = 1 := by
  simp [prefixSum, ht₁]

#print axioms totalSum_eq_prefix_add_last
#print axioms last_sum_iff_last_coordinate
#print axioms truncate_reinsertLast
#print axioms reinsert_truncate_of_original_sum
#print axioms original_implies_eliminated
#print axioms eliminated_implies_original
#print axioms boundary_r2

end Carlet.QuadraticV7
