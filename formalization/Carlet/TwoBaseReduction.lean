import Carlet.LowDimensionReduction
import Carlet.KloostermanThree

namespace Carlet

/-- The original conjecture is equivalent to its two remaining lower-half families. -/
theorem oddCarletConjecture_iff_four_and_five :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n → (k = 4 ∨ k = 5) → 2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk hbound K _ _ _ hcard
    apply h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_small_dimensions.mpr
    intro n k hn hk hk5 hbound K _ _ _ hcard
    by_cases h3 : k = 3
    · subst k
      exact hasZeroSumSubspace_three n (finrank_eq_of_card n hcard) hn (by omega)
    · exact h n k hn (by omega) hbound K hcard

#print axioms oddCarletConjecture_iff_four_and_five

end Carlet
