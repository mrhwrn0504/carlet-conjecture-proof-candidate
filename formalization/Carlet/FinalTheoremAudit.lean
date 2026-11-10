import Carlet.MainTheorem
import Carlet.EvenDegree
import Carlet.FullTheorem

namespace Carlet

/-- Independently elaborate the original fully quantified odd-degree statement. -/
theorem independently_checked_original_statement :
    ∀ (n k : ℕ), Odd n → 3 ≤ k → k + 3 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K k :=
  oddCarletConjecture_main

/-- Independently elaborate the full even-degree statement, including k = 2. -/
theorem independently_checked_even_degree_statement :
    ∀ (n : ℕ), Even n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n →
          ∀ k : ℕ, 2 ≤ k → k + 2 ≤ n → HasZeroSumSubspace K k := by
  classical
  intro n hn K _ _ _ hcard k hk hkmax
  exact evenDegreeCarlet_unconditional n hn K hcard k hk hkmax

/-- Independent check of the parity-sensitive combined theorem. -/
theorem independently_checked_full_parity_statement :
    ∀ (n k : ℕ),
      ((Even n ∧ 2 ≤ k ∧ k + 2 ≤ n) ∨
       (Odd n ∧ 3 ≤ k ∧ k + 3 ≤ n)) →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
        [DecidableEq K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K k :=
  carletConjecture_full

/-- Independent check of the common n ≥ 6 specialization. -/
theorem independently_checked_common_range_statement :
    ∀ (n k : ℕ), 6 ≤ n → 3 ≤ k → k + 3 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
        [DecidableEq K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K k :=
  carletConjecture_n_ge6

#check oddCarletConjecture_main
#print axioms oddCarletConjecture_main
#print axioms oddCarletConjecture_original_statement
#print axioms independently_checked_original_statement
#check evenDegreeCarlet_unconditional
#print axioms evenDegreeCarlet_unconditional
#print axioms independently_checked_even_degree_statement
#check carletConjecture_full
#print axioms carletConjecture_full
#print axioms independently_checked_full_parity_statement
#check carletConjecture_n_ge6
#print axioms carletConjecture_n_ge6
#print axioms independently_checked_common_range_statement

end Carlet
