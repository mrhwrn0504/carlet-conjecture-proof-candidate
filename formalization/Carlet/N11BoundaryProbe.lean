import Carlet.RemainingCases11Four

noncomputable section
namespace Carlet

/-- Every original conjecture dimension is covered when n = 11. -/
theorem oddCarlet_at_eleven (k : ℕ) (hk : 3 ≤ k) (hkn : k + 3 ≤ 11)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2 ^ 11) : HasZeroSumSubspace K k := by
  classical
  have h3 : HasZeroSumSubspace K 3 :=
    hasZeroSumSubspace_three 11 (finrank_eq_of_card 11 hcard) (by decide) (by decide)
  have h4 : HasZeroSumSubspace K 4 := hasZeroSumSubspace_n11_four_card_probe hcard
  have h5 : HasZeroSumSubspace K 5 := hasZeroSumSubspace_n11_card_probe hcard
  have hcases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3
  · exact h4
  · exact h5
  · exact (zeroSumSubspace_complement_of_card 11 6 hcard (by omega) (by omega)).mpr (by simpa using h5)
  · exact (zeroSumSubspace_complement_of_card 11 7 hcard (by omega) (by omega)).mpr (by simpa using h4)
  · exact (zeroSumSubspace_complement_of_card 11 8 hcard (by omega) (by omega)).mpr (by simpa using h3)

#print axioms oddCarlet_at_eleven
end Carlet
