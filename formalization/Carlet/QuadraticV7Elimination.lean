import Mathlib

/-!
# Carlet v7: direct elimination of the final reciprocal coordinate

The only eliminated coordinate is t_r.  No auxiliary s_i or v_{a,j}
coordinates are introduced.  The lemmas are stated over an arbitrary
commutative ring equipped with the characteristic-two equation 2 = 0.
-/

open scoped BigOperators

namespace Carlet.QuadraticV7

variable {A : Type*} [CommRing A]

/-- The contribution of t₂,…,t_{r-1}. -/
def prefixSum (t : ℕ → A) (r : ℕ) : A :=
  ∑ i ∈ Finset.range (r - 2), t (i + 2)

/-- The contribution of t₂,…,t_r. -/
def totalSum (t : ℕ → A) (r : ℕ) : A :=
  ∑ i ∈ Finset.range (r - 1), t (i + 2)

/-- Splitting off the final summand is valid also at the boundary r = 2. -/
theorem totalSum_eq_prefix_add_last (t : ℕ → A) (r : ℕ) (hr : 2 ≤ r) :
    totalSum t r = prefixSum t r + t r := by
  unfold totalSum prefixSum
  have hr₁ : r - 1 = (r - 2) + 1 := by omega
  have hr₂ : r - 2 + 2 = r := by omega
  rw [hr₁, Finset.sum_range_succ, hr₂]

/-- In characteristic two, every element is its own additive inverse. -/
theorem add_self_eq_zero_of_two_eq_zero (h₂ : (2 : A) = 0) (x : A) :
    x + x = 0 := by
  calc
    x + x = (2 : A) * x := by ring
    _ = 0 := by rw [h₂]; simp

/--
The final zero-sum equation is equivalent to the explicit value of t_r.
This is the algebraic step that eliminates t_r.
-/
theorem last_sum_iff_last_coordinate (t : ℕ → A) (r : ℕ) (hr : 2 ≤ r)
    (h₂ : (2 : A) = 0) :
    1 + totalSum t r = 0 ↔ t r = 1 + prefixSum t r := by
  rw [totalSum_eq_prefix_add_last t r hr]
  constructor
  · intro h
    have hself := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSum t r)
    calc
      t r = (1 + prefixSum t r) +
          (1 + prefixSum t r + t r) := by
        calc
          t r = 0 + t r := by simp
          _ = ((1 + prefixSum t r) + (1 + prefixSum t r)) + t r := by
            rw [hself]
            simp
          _ = (1 + prefixSum t r) +
              (1 + prefixSum t r + t r) := by ac_rfl
      _ = (1 + (prefixSum t r + t r)) + (1 + prefixSum t r) := by ac_rfl
      _ = 0 + (1 + prefixSum t r) := by rw [h]
      _ = 1 + prefixSum t r := by simp
  · intro htr
    rw [htr]
    have hself := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSum t r)
    calc
      1 + (prefixSum t r + (1 + prefixSum t r)) =
          (1 + prefixSum t r) + (1 + prefixSum t r) := by ac_rfl
      _ = 0 := hself

/-- Reinsert the eliminated coordinate by its forced polynomial expression. -/
def reinsertLast (t : ℕ → A) (r : ℕ) (i : ℕ) : A :=
  if i = r then 1 + prefixSum t r else t i

theorem prefixSum_reinsertLast (t : ℕ → A) (r : ℕ) (hr : 2 ≤ r) :
    prefixSum (reinsertLast t r) r = prefixSum t r := by
  unfold prefixSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < r - 2 := Finset.mem_range.mp hi
  have hne : i + 2 ≠ r := by omega
  simp [reinsertLast, hne]

theorem totalSum_reinsertLast (t : ℕ → A) (r : ℕ) (hr : 2 ≤ r) :
    totalSum (reinsertLast t r) r =
      prefixSum t r + (1 + prefixSum t r) := by
  rw [totalSum_eq_prefix_add_last (reinsertLast t r) r hr]
  rw [prefixSum_reinsertLast t r hr]
  simp [reinsertLast]

/-- The triangular Artin–Schreier equations; the diagonal is fixed to one. -/
def TriangularRelations (u : ℕ → ℕ → A) (c : ℕ → A) (r : ℕ) : Prop :=
  (∀ a, 2 ≤ a → a ≤ r → u a a = 1) ∧
  (∀ a, 2 ≤ a → a ≤ r → ∀ j, 1 ≤ j → j < a →
    u a j ^ 2 + u a j = c j * u a (j + 1))

/-- Original system before eliminating t_r. -/
def OriginalSystem (u : ℕ → ℕ → A) (t c : ℕ → A) (r : ℕ) : Prop :=
  TriangularRelations u c r ∧
  (∀ j, 1 ≤ j → j < r → c j * t (j + 1) = t j) ∧
  t 1 = 1 ∧
  1 + totalSum t r = 0

/-- v7 system after direct elimination of t_r. -/
def EliminatedSystem (u : ℕ → ℕ → A) (t c : ℕ → A) (r : ℕ) : Prop :=
  TriangularRelations u c r ∧
  (∀ j, 1 ≤ j → j + 1 < r → c j * t (j + 1) = t j) ∧
  t 1 = 1 ∧
  c (r - 1) * (1 + prefixSum t r) = t (r - 1)

/--
Every solution of the original system already has the forced value of t_r,
so deleting that coordinate gives a solution of the v7 equations.
-/
theorem original_implies_eliminated (u : ℕ → ℕ → A) (t c : ℕ → A)
    (r : ℕ) (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (h : OriginalSystem u t c r) : EliminatedSystem u t c r := by
  rcases h with ⟨hu, hratio, ht₁, hsum⟩
  have htr := (last_sum_iff_last_coordinate t r hr h₂).mp hsum
  refine ⟨hu, ?_, ht₁, ?_⟩
  · intro j hj₁ hjr
    exact hratio j hj₁ (by omega)
  · have hlast := hratio (r - 1) (by omega) (by omega)
    have hlast' : c (r - 1) * t r = t (r - 1) := by
      simpa [show r - 1 + 1 = r by omega] using hlast
    simpa [htr] using hlast'

/--
Conversely, a v7 point determines a unique value for the deleted coordinate;
reinstating it gives a point of the original system.
-/
theorem eliminated_implies_original (u : ℕ → ℕ → A) (t c : ℕ → A)
    (r : ℕ) (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (h : EliminatedSystem u t c r) :
    OriginalSystem u (reinsertLast t r) c r := by
  rcases h with ⟨hu, hratio, ht₁, hlast⟩
  refine ⟨hu, ?_, ?_, ?_⟩
  · intro j hj₁ hjr
    by_cases hlastIndex : j + 1 = r
    · have hj : j = r - 1 := by omega
      subst j
      simpa [reinsertLast, show r - 1 + 1 = r by omega,
        show r - 1 ≠ r by omega] using hlast
    · have hjNext : j + 1 < r := by omega
      have hjNe : j ≠ r := by omega
      have hjNextNe : j + 1 ≠ r := by omega
      simpa [reinsertLast, hjNe, hjNextNe] using hratio j hj₁ hjNext
  · have hrNe : 1 ≠ r := by omega
    simpa [reinsertLast, hrNe] using ht₁
  · rw [totalSum_reinsertLast t r hr]
    have hself := add_self_eq_zero_of_two_eq_zero (A := A) h₂
      (1 + prefixSum t r)
    calc
      1 + (prefixSum t r + (1 + prefixSum t r)) =
          (1 + prefixSum t r) + (1 + prefixSum t r) := by ac_rfl
      _ = 0 := hself

/-- Reinserted and original coordinates agree below the deleted index. -/
theorem reinsertLast_eq_below (t : ℕ → A) (r i : ℕ) (hi : i < r) :
    reinsertLast t r i = t i := by
  simp [reinsertLast, Nat.ne_of_lt hi]

/--
If the original zero-sum equation holds, reinsertion changes no coordinate:
the original t_r was already forced to be the v7 expression.
-/
theorem reinsertLast_eq_self_of_original_sum (t : ℕ → A) (r : ℕ)
    (hr : 2 ≤ r) (h₂ : (2 : A) = 0)
    (hsum : 1 + totalSum t r = 0) :
    reinsertLast t r = t := by
  have htr := (last_sum_iff_last_coordinate t r hr h₂).mp hsum
  funext i
  by_cases hi : i = r
  · subst i
    simp [reinsertLast, htr]
  · simp [reinsertLast, hi]

/-- The boundary case r = 2 reduces exactly to c₁ = 1. -/
theorem boundary_r2 (t c : ℕ → A) (ht₁ : t 1 = 1) :
    c 1 * (1 + prefixSum t 2) = t 1 ↔ c 1 = 1 := by
  simp [prefixSum, ht₁]

#print axioms totalSum_eq_prefix_add_last
#print axioms last_sum_iff_last_coordinate
#print axioms original_implies_eliminated
#print axioms eliminated_implies_original
#print axioms reinsertLast_eq_self_of_original_sum
#print axioms boundary_r2

end Carlet.QuadraticV7
