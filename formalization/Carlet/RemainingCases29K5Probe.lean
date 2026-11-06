import Carlet.N29K5CompleteProbe
import Carlet.N29K5FieldBridgeProbe
import Carlet.RemainingCases23K5Probe
import Carlet.RemainingCases11Four
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

open Carlet
noncomputable section
namespace Carlet

local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩

/-- The degree-29 construction embeds into every finite extension whose
    F₂-dimension is divisible by 29. -/
theorem hasZeroSumSubspace_five_of_29_dvd_card {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hdiv : 29 ∣ n) :
    HasZeroSumSubspace K 5 := by
  classical
  let L := AdjoinRoot f29K5
  have hr : Module.finrank (ZMod 2) L = 29 := by
    have hc : Fintype.card L = 2 ^ 29 := by simpa [L] using adjoinRoot29K5_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hc
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hc
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, finrank_eq_of_card n hcard] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 5
    hasZeroSumSubspace_2pow29_five_probe

/-- The k=5 residual interface after also removing multiples of 29. -/
theorem oddCarletConjecture_iff_remaining_after_five_29 :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 15 ∣ n ∧ ¬ 17 ∣ n ∧ ¬ 19 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 17 ∣ n ∧
            ¬ 19 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 29 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_remaining_after_five_9.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with ⟨hk, h7, h13, h15, h17, h19⟩ |
      ⟨hk, h5, h9, h11, h13, h17, h19, h21, h31⟩
    · exact h n k hn (Or.inl ⟨hk, h7, h13, h15, h17, h19⟩) hb K hcard
    · by_cases h29 : 29 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_29_dvd_card n hcard h29
      · exact h n k hn (Or.inr ⟨hk, h5, h9, h11, h13, h17, h19, h21, h29, h31⟩)
          hb K hcard

/-- Combined residual interface: the degree-23 and degree-29 constructions
    both remove their divisibility families from the k=5 obligations. -/
theorem oddCarletConjecture_iff_remaining_after_five_23_29 :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 15 ∣ n ∧ ¬ 17 ∣ n ∧ ¬ 19 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 17 ∣ n ∧
            ¬ 19 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 23 ∣ n ∧ ¬ 29 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_remaining_after_five_23.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with ⟨hk, h7, h13, h15, h17, h19⟩ |
      ⟨hk, h5, h9, h11, h13, h17, h19, h21, h23, h31⟩
    · exact h n k hn (Or.inl ⟨hk, h7, h13, h15, h17, h19⟩) hb K hcard
    · by_cases h29 : 29 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_29_dvd_card n hcard h29
      · exact h n k hn
          (Or.inr ⟨hk, h5, h9, h11, h13, h17, h19, h21, h23, h29, h31⟩)
          hb K hcard

/-- Combined remaining cases after all currently wired k=4 and k=5
    divisibility families have been removed. -/
theorem oddCarletConjecture_iff_remaining_combined :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 15 ∣ n ∧
            ¬ 17 ∣ n ∧ ¬ 19 ∣ n ∨
          k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 9 ∣ n ∧ ¬ 11 ∣ n ∧ ¬ 13 ∣ n ∧ ¬ 17 ∣ n ∧
            ¬ 19 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 23 ∣ n ∧ ¬ 29 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_remaining_after_five_23_29.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with ⟨hk, h7, h13, h15, h17, h19⟩ |
      ⟨hk, h5, h9, h11, h13, h17, h19, h21, h23, h29, h31⟩
    · by_cases h9 : 9 ∣ n
      · subst k
        exact hasZeroSumSubspace_four_of_9_dvd_card n hcard h9
      · by_cases h11 : 11 ∣ n
        · subst k
          exact hasZeroSumSubspace_four_of_11_dvd_card n hcard h11
        · exact h n k hn (Or.inl ⟨hk, h7, h9, h11, h13, h15, h17, h19⟩)
            hb K hcard
    · exact h n k hn
        (Or.inr ⟨hk, h5, h9, h11, h13, h17, h19, h21, h23, h29, h31⟩)
        hb K hcard

#print axioms hasZeroSumSubspace_five_of_29_dvd_card
#print axioms oddCarletConjecture_iff_remaining_after_five_29
#print axioms oddCarletConjecture_iff_remaining_after_five_23_29
#print axioms oddCarletConjecture_iff_remaining_combined
end Carlet
