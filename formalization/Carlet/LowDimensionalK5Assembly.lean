import Carlet.K4AllOddDegreesProbe
import Carlet.RemainingCasesK5Below37

noncomputable section
namespace Carlet

/-- The original conjecture reduces to the sole general k=5 family with
    odd degree at least 37: all smaller admissible odd degrees are discharged
    by the existing finite constructions and divisibility families. -/
theorem oddCarletConjecture_of_five_large
    (h5 : ∀ (n : ℕ), Odd n → 37 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K 5) :
    OddCarletConjecture := by
  apply oddCarletConjecture_of_five
  intro n hn hmin K _ _ _ hcard
  by_cases hsmall : n < 37
  · exact hasZeroSumSubspace_five_of_odd_card_lt37 n hn (by omega) hsmall K hcard
  · exact h5 n hn (by omega) K hcard

#print axioms oddCarletConjecture_of_five_large

end Carlet
