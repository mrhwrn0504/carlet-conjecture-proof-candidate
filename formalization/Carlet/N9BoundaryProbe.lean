import Carlet.RemainingCases9

noncomputable section
namespace Carlet

/-- Every original conjecture dimension is covered when n = 9. -/
theorem oddCarlet_at_nine (k : ℕ) (hk : 3 ≤ k) (hkn : k + 3 ≤ 9)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2 ^ 9) : HasZeroSumSubspace K k := by
  classical
  have h3 : HasZeroSumSubspace K 3 :=
    hasZeroSumSubspace_three 9 (finrank_eq_of_card 9 hcard) (by decide) (by decide)
  have h4 : HasZeroSumSubspace K 4 := hasZeroSumSubspace_n9_four_card_probe hcard
  have hcases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact h3
  · exact h4
  · exact (zeroSumSubspace_complement_of_card 9 5 hcard (by omega) (by omega)).mpr (by simpa using h4)
  · exact (zeroSumSubspace_complement_of_card 9 6 hcard (by omega) (by omega)).mpr (by simpa using h3)

#print axioms oddCarlet_at_nine
end Carlet
