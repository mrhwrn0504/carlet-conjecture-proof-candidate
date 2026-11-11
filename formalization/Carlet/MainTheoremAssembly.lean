import Carlet.RemainingCases29K5Probe

noncomputable section
namespace Carlet

/-- The original conjecture follows from precisely the two remaining
    low-dimensional families. The hypotheses are explicit and are not
    claimed to be proved here. -/
theorem oddCarletConjecture_of_four_five
    (h4 : ∀ (n : ℕ), Odd n → 9 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K 4)
    (h5 : ∀ (n : ℕ), Odd n → 11 ≤ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
        Fintype.card K = 2 ^ n → HasZeroSumSubspace K 5) :
    OddCarletConjecture := by
  classical
  apply oddCarletConjecture_iff_small_dimensions.mpr
  intro n k hn hk hk5 hbound K _ _ _ hcard
  have h3 : HasZeroSumSubspace K 3 := by
    have hfin := finrank_eq_of_card (K := K) n hcard
    exact hasZeroSumSubspace_three n hfin hn (by omega)
  by_cases hk3 : k = 3
  · simpa [hk3] using h3
  by_cases hk4 : k = 4
  · subst k
    exact h4 n hn (by omega) K hcard
  have hk5' : k = 5 := by omega
  subst k
  exact h5 n hn (by omega) K hcard

#print axioms oddCarletConjecture_of_four_five
end Carlet
