import Carlet.MainTheorem
import Carlet.EvenDegree

namespace Carlet

/-- Independently elaborate the original fully quantified statement against
    the final theorem without adding any hypotheses. -/
theorem independently_checked_original_statement :
    ∀ (n k : ℕ), Odd n → 3 ≤ k → k + 3 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K k :=
  oddCarletConjecture_main

/-- Independently elaborate the even-degree theorem with its exact quantifiers,
    including the full k=2 edge of Theorem 5.2. -/
theorem independently_checked_even_degree_statement :
    ∀ (n : ℕ), Even n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n →
          ∀ k : ℕ, 2 ≤ k → k + 2 ≤ n → HasZeroSumSubspace K k := by
  classical
  intro n hn K _ _ _ hcard k hk hkmax
  exact evenDegreeCarlet_unconditional n hn K hcard k hk hkmax

#check oddCarletConjecture_main
#print axioms oddCarletConjecture_main
#print axioms oddCarletConjecture_original_statement
#print axioms independently_checked_original_statement
#check evenDegreeCarlet_unconditional
#print axioms evenDegreeCarlet_unconditional
#print axioms independently_checked_even_degree_statement
end Carlet
