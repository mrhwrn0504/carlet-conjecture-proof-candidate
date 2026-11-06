import Carlet.N19K5CompleteProbe
import Carlet.RemainingCases17Four

noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩

namespace Carlet

theorem hasZeroSumSubspace_five_of_19_dvd_card {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hdiv : 19 ∣ n) :
    HasZeroSumSubspace K 5 := by
  classical
  let L := AdjoinRoot f19
  have hr : Module.finrank (ZMod 2) L = 19 := by
    have hc : Fintype.card L = 2 ^ 19 := by simpa [L] using adjoinRoot19_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hc
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hc
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, finrank_eq_of_card n hcard] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom13_probe e e.injective 5
    hasZeroSumSubspace_524288_probe

theorem oddCarletConjecture_iff_remaining_after_five_19 :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 15 ∣ n ∧ ¬ 17 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 17 ∣ n ∧
            ¬ 19 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_remaining_after_four_17.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with ⟨hk, h7, h13, h15, h17⟩ | ⟨hk, h5, h11, h13, h17, h21, h31⟩
    · exact h n k hn (Or.inl ⟨hk, h7, h13, h15, h17⟩) hb K hcard
    · by_cases h19 : 19 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_19_dvd_card n hcard h19
      · exact h n k hn (Or.inr ⟨hk, h5, h11, h13, h17, h19, h21, h31⟩) hb K hcard

#print axioms hasZeroSumSubspace_five_of_19_dvd_card
#print axioms oddCarletConjecture_iff_remaining_after_five_19
end Carlet
