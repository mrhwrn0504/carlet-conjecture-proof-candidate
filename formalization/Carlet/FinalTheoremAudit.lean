import Carlet.MainTheorem

namespace Carlet

/-- Independently elaborate the original fully quantified statement against
    the final theorem without adding any hypotheses. -/
theorem independently_checked_original_statement :
    ∀ (n k : ℕ), Odd n → 3 ≤ k → k + 3 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K k :=
  oddCarletConjecture_main

#check oddCarletConjecture_main
#print axioms oddCarletConjecture_main
#print axioms oddCarletConjecture_original_statement
#print axioms independently_checked_original_statement
end Carlet
