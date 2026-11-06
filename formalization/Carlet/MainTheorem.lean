import Carlet.K5NormOneConstructionProbe

noncomputable section
namespace Carlet

/-- Carlet's original odd-degree statement from `Statement.lean`. -/
theorem oddCarletConjecture_main : OddCarletConjecture :=
  oddCarletConjecture_normOne

/-- An explicit copy of all original quantifiers and hypotheses, checked by
    Lean against the proved theorem. -/
theorem oddCarletConjecture_original_statement :
    ∀ (n k : ℕ), Odd n → 3 ≤ k → k + 3 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K k :=
  oddCarletConjecture_main

#print OddCarletConjecture
#print oddCarletConjecture_original_statement
#print axioms oddCarletConjecture_main
#print axioms oddCarletConjecture_original_statement
end Carlet
