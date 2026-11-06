import Carlet.N9K5SubfieldProbe
import Carlet.RemainingCases19Four
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
namespace Carlet
theorem oddCarletConjecture_iff_remaining_after_five_9 :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 15 ∣ n ∧ ¬ 17 ∣ n ∧ ¬ 19 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 17 ∣ n ∧
            ¬ 19 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  constructor
  · intro h n k hn hk hb K inst1 inst2 inst3 hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_remaining_after_four_19.mpr
    intro n k hn hk hb K inst1 inst2 inst3 hcard
    rcases hk with ⟨hk, h7, h13, h15, h17⟩ |
      ⟨hk, h5, h11, h13, h17, h19, h21, h31⟩
    · exact h n k hn (Or.inl ⟨hk, h7, h13, h15, h17⟩) hb K hcard
    · by_cases hdiv : 9 ∣ n
      · subst k
        have hfin := finrank_eq_of_card (K := K) n hcard
        exact hasZeroSumSubspace_five_of_9_dvd n hfin hdiv
      · exact h n k hn (Or.inr ⟨hk, h5, hdiv, h11, h13, h17, h19, h21, h31⟩) hb K hcard
#print axioms oddCarletConjecture_iff_remaining_after_five_9
end Carlet



