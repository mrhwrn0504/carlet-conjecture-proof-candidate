import Carlet.Elementary
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Exact finite-field statement. This file defines the conjecture; it does
not assert an unproved theorem or introduce an axiom for the main result. -/

noncomputable section

open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

def underlyingFinset (E : Submodule (ZMod 2) K) : Finset K := by
  classical
  exact Finset.univ.filter (fun x => x ∈ E)

@[simp] theorem mem_underlyingFinset (E : Submodule (ZMod 2) K) (x : K) :
    x ∈ underlyingFinset E ↔ x ∈ E := by
  classical
  simp [underlyingFinset]

def IsZeroSum (E : Submodule (ZMod 2) K) : Prop := by
  classical
  exact (∑ x ∈ (underlyingFinset E).erase 0, x⁻¹) = 0

def HasZeroSumSubspace (K : Type*) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (k : ℕ) : Prop :=
  ∃ E : Submodule (ZMod 2) K, Module.finrank (ZMod 2) E = k ∧ IsZeroSum E

/-- Every choice of a finite field of size 2^n is covered; k+3≤n is the
untruncated form of k≤n−3 in the permitted range. This is an open target. -/
def OddCarletConjecture : Prop :=
  ∀ (n k : ℕ), Odd n → 3 ≤ k → k + 3 ≤ n →
    ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
      Fintype.card K = 2 ^ n → HasZeroSumSubspace K k

/-- The already-proved coefficient criterion specializes to actual
F₂-linear subspaces without any assumption of the conjecture. -/
theorem zeroSum_iff_coeff_two (E : Submodule (ZMod 2) K) :
    IsZeroSum E ↔ (rootProduct (underlyingFinset E)).coeff 2 = 0 := by
  classical
  exact inverse_sum_eq_zero_iff_rootProduct_coeff_two _ (by simp)

#print OddCarletConjecture
#print axioms zeroSum_iff_coeff_two

end Carlet
