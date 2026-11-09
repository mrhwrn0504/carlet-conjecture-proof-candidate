import Mathlib

/-!
# Carlet v7: direct elimination of the final reciprocal coordinate

The only eliminated coordinate is t_r.  No auxiliary s_i or v_{a,j}
coordinates are introduced.

The original t-vector is indexed by Fin r (slots t₁,…,t_r), and the v7
t-vector by Fin (r-1) (slots t₁,…,t_{r-1}).  The first slot t₁ is fixed
to 1 in both systems; it is retained only to make the endpoint equations
uniform.  Thus the actual free t-coordinates drop by exactly one.
-/

open scoped BigOperators

namespace Carlet.QuadraticV7

variable {A : Type*} [CommRing A]

/-- Evaluate a finite coordinate vector at a natural index, returning zero out of range. -/
def evalFin (n : ℕ) (t : Fin n → A) (i : ℕ) : A :=
  if h : i < n then t ⟨i, h⟩ else 0

/-- The retained contribution t₂ + ⋯ + t_{r-1}. -/
def prefixSum (r : ℕ) (t : Fin (r - 1) → A) : A :=
  ∑ i ∈ Finset.range (r - 2), evalFin (r - 1) t (i + 1)

/-- The same prefix, viewed in the original coordinate space. -/
def prefixSumOriginal (r : ℕ) (t : Fin r → A) : A :=
  ∑ i ∈ Finset.range (r - 2), evalFin r t (i + 1)

/-- The original contribution t₂ + ⋯ + t_r. -/
def totalSum (r : ℕ) (t : Fin r → A) : A :=
  ∑ i ∈ Finset.range (r - 1), evalFin r t (i + 1)

/-- The last original coordinate t_r. -/
def lastCoordinate (r : ℕ) (t : Fin r → A) (hr : 1 ≤ r) : A :=
  t ⟨r - 1, by omega⟩

/-- Restrict the original coordinates to t₁,…,t_{r-1}. -/
def truncate (r : ℕ) (t : Fin r → A) : Fin (r - 1) → A :=
  fun i => t ⟨i.val, by omega⟩

/-- Splitting off t_r from the original finite sum. -/
theorem totalSum_eq_prefix_add_last (r : ℕ) (t : Fin r → A)
    (hr : 2 ≤ r) :
    totalSum r t = prefixSumOriginal r t + lastCoordinate r t (by omega) := by
  unfold totalSum prefixSumOriginal lastCoordinate
  rw [show r - 1 = (r - 2) + 1 by omega, Finset.sum_range_succ]
  have hlast : evalFin r t ((r - 2) + 1) = t ⟨r - 1, by omega⟩ := by
    simp [evalFin, show r - 2 + 1 = r - 1 by omega]
  rw [hlast]

/-- Restricting to the first r-1 coordinates preserves the prefix sum. -/
theorem prefixSum_truncate (r : ℕ) (t : Fin r → A) :
    prefixSum r (truncate r t) = prefixSumOriginal r t := by
  unfold prefixSum prefixSumOriginal truncate
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < r - 2 := Finset.mem_range.mp hi
  have hlt : i + 1 < r - 1 := by omega
  have hlt' : i + 1 < r := by omega
  simp [evalFin, hlt, hlt', truncate]

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
theorem last_sum_iff_last_coordinate (r : ℕ) (t : Fin r → A)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0) :
    1 + totalSum r t = 0 ↔
      lastCoordinate r t (by omega) = 1 + prefixSumOriginal r t := by
  rw [totalSum_eq_prefix_add_last r t hr]
  constructor
  · intro h
    have hx := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSumOriginal r t)
    have hsum : lastCoordinate r t (by omega) +
        (1 + prefixSumOriginal r t) = 0 := by
      simpa [add_assoc, add_comm, add_left_comm] using h
    calc
      lastCoordinate r t (by omega) =
          lastCoordinate r t (by omega) + 0 := by simp
      _ = lastCoordinate r t (by omega) +
          ((1 + prefixSumOriginal r t) +
            (1 + prefixSumOriginal r t)) := by rw [hx]; simp
      _ = (lastCoordinate r t (by omega) +
            (1 + prefixSumOriginal r t)) +
            (1 + prefixSumOriginal r t) := by ac_rfl
      _ = 0 + (1 + prefixSumOriginal r t) := by rw [hsum]
      _ = 1 + prefixSumOriginal r t := by simp
  · intro hlast
    have hx := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSumOriginal r t)
    calc
      1 + (prefixSumOriginal r t + lastCoordinate r t (by omega)) =
          (1 + prefixSumOriginal r t) +
            (1 + prefixSumOriginal r t) := by rw [hlast]; ac_rfl
      _ = 0 := hx

/-- Reinsert the deleted coordinate using its forced polynomial expression. -/
def reinsertLast (r : ℕ) (t : Fin (r - 1) → A)
    (hr : 2 ≤ r) : Fin r → A :=
  fun i =>
    if hi : i.val = r - 1 then
      1 + prefixSum r t
    else
      t ⟨i.val, by omega⟩

/-- The reinserted point has exactly the retained prefix sum. -/
theorem prefixSum_reinsertLast (r : ℕ) (t : Fin (r - 1) → A)
    (hr : 2 ≤ r) :
    prefixSumOriginal r (reinsertLast r t hr) = prefixSum r t := by
  unfold prefixSumOriginal prefixSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < r - 2 := Finset.mem_range.mp hi
  have hlt : i + 1 < r - 1 := by omega
  have hlt' : i + 1 < r := by omega
  have hne : i + 1 ≠ r - 1 := by omega
  simp [evalFin, hlt, hlt', reinsertLast, hne]

/-- The original total sum after reinsertion is prefix plus the forced last term. -/
theorem totalSum_reinsertLast (r : ℕ) (t : Fin (r - 1) → A)
    (hr : 2 ≤ r) :
    totalSum r (reinsertLast r t hr) =
      prefixSum r t + (1 + prefixSum r t) := by
  rw [totalSum_eq_prefix_add_last r (reinsertLast r t hr) hr]
  rw [prefixSum_reinsertLast r t hr]
  simp [lastCoordinate, reinsertLast]

/-- Truncating after reinsertion recovers every retained coordinate. -/
theorem truncate_reinsertLast (r : ℕ) (t : Fin (r - 1) → A)
    (hr : 2 ≤ r) :
    truncate r (reinsertLast r t hr) = t := by
  funext i
  have hne : i.val ≠ r - 1 := by omega
  simp [truncate, reinsertLast, hne]

/-- Truncating an original point and reinserting it recovers it under the sum equation. -/
theorem reinsert_truncate_of_original_sum (r : ℕ) (t : Fin r → A)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (hsum : 1 + totalSum r t = 0) :
    reinsertLast r (truncate r t) hr = t := by
  have hlast := (last_sum_iff_last_coordinate r t hr h₂).mp hsum
  have hprefix := prefixSum_truncate r t
  funext i
  by_cases hi : i.val = r - 1
  · have hiEq : i = ⟨r - 1, by omega⟩ := Fin.ext hi
    subst i
    change 1 + prefixSum r (truncate r t) = lastCoordinate r t (by omega)
    rw [hprefix]
    exact hlast.symm
  · simp [reinsertLast, hi, truncate]

def TriangularRelations (u : ℕ → ℕ → A) (c : ℕ → A) (r : ℕ) : Prop :=
  (∀ a, 2 ≤ a → a ≤ r → u a a = 1) ∧
  (∀ a, 2 ≤ a → a ≤ r → ∀ j, 1 ≤ j → j < a →
    u a j ^ 2 + u a j = c j * u a (j + 1))

def OriginalSystem (r : ℕ) (hr : 2 ≤ r) (u : ℕ → ℕ → A)
    (t : Fin r → A) (c : ℕ → A) : Prop :=
  TriangularRelations u c r ∧
  (∀ j : Fin (r - 1),
    c (j.val + 1) * t ⟨j.val + 1, by omega⟩ =
      t ⟨j.val, by omega⟩) ∧
  t ⟨0, by omega⟩ = 1 ∧
  1 + totalSum r t = 0

def EliminatedSystem (r : ℕ) (hr : 2 ≤ r) (u : ℕ → ℕ → A)
    (t : Fin (r - 1) → A) (c : ℕ → A) : Prop :=
  TriangularRelations u c r ∧
  (∀ j : Fin (r - 2),
    c (j.val + 1) * t ⟨j.val + 1, by omega⟩ =
      t ⟨j.val, by omega⟩) ∧
  t ⟨0, by omega⟩ = 1 ∧
  c (r - 1) * (1 + prefixSum r t) =
    t ⟨r - 2, by omega⟩

theorem original_implies_eliminated (r : ℕ) (hr : 2 ≤ r)
    (u : ℕ → ℕ → A) (t : Fin r → A) (c : ℕ → A)
    (h₂ : (2 : A) = 0)
    (h : OriginalSystem r hr u t c) :
    EliminatedSystem r hr u (truncate r t) c := by
  rcases h with ⟨hu, hratio, ht₁, hsum⟩
  have hlastValue := (last_sum_iff_last_coordinate r t hr h₂).mp hsum
  have hlastRatio :
      c (r - 1) * lastCoordinate r t (by omega) =
        t ⟨r - 2, by omega⟩ := by
    have h := hratio ⟨r - 2, by omega⟩
    simpa [lastCoordinate, show r - 2 + 1 = r - 1 by omega] using h
  refine ⟨hu, ?_, ?_, ?_⟩
  · intro j
    have h := hratio ⟨j.val, by omega⟩
    simpa [truncate] using h
  · simpa [truncate] using ht₁
  · calc
      c (r - 1) * (1 + prefixSum r (truncate r t)) =
          c (r - 1) * lastCoordinate r t (by omega) := by
            rw [prefixSum_truncate r t, ← hlastValue]
      _ = t ⟨r - 2, by omega⟩ := hlastRatio
      _ = truncate r t ⟨r - 2, by omega⟩ := by rfl

theorem eliminated_implies_original (r : ℕ) (hr : 2 ≤ r)
    (u : ℕ → ℕ → A) (t : Fin (r - 1) → A) (c : ℕ → A)
    (h₂ : (2 : A) = 0)
    (h : EliminatedSystem r hr u t c) :
    OriginalSystem r hr u (reinsertLast r t hr) c := by
  rcases h with ⟨hu, hratio, ht₁, hlast⟩
  refine ⟨hu, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val = r - 2
    · have hjEq : j = ⟨r - 2, by omega⟩ := Fin.ext hj
      rw [hjEq]
      simpa [reinsertLast, show r - 2 + 1 = r - 1 by omega] using hlast
    · have hjlt : j.val < r - 2 := by omega
      have h := hratio ⟨j.val, hjlt⟩
      have hne₀ : j.val ≠ r - 1 := by omega
      have hne₁ : j.val + 1 ≠ r - 1 := by omega
      simpa [reinsertLast, hne₀, hne₁] using h
  · have hne : 0 ≠ r - 1 := by omega
    simpa [reinsertLast, hne] using ht₁
  · calc
      1 + totalSum r (reinsertLast r t hr) =
          1 + (prefixSum r t + (1 + prefixSum r t)) := by
            rw [totalSum_reinsertLast r t hr]
      _ = 0 := by
        have hx := add_self_eq_zero_of_two_eq_zero (A := A) h₂
          (1 + prefixSum r t)
        calc
          1 + (prefixSum r t + (1 + prefixSum r t)) =
              (1 + prefixSum r t) + (1 + prefixSum r t) := by ac_rfl
          _ = 0 := hx

theorem boundary_r2 (t : Fin 1 → A) (c : ℕ → A)
    (ht₁ : t ⟨0, by omega⟩ = 1) :
    c 1 * (1 + prefixSum 2 t) = t ⟨0, by omega⟩ ↔ c 1 = 1 := by
  simp [prefixSum, ht₁]

#print axioms totalSum_eq_prefix_add_last
#print axioms last_sum_iff_last_coordinate
#print axioms truncate_reinsertLast
#print axioms reinsert_truncate_of_original_sum
#print axioms original_implies_eliminated
#print axioms eliminated_implies_original
#print axioms boundary_r2

end Carlet.QuadraticV7
