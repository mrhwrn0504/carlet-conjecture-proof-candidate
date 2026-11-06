import Carlet.N23FourASBridgeProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

/-- The precise k=4 slice of the original odd-degree statement. -/
def OddFourCarlet : Prop :=
  ∀ (n : ℕ), Odd n → 7 ≤ n →
    ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
      Fintype.card K = 2 ^ n → HasZeroSumSubspace K 4

theorem oddFourCarlet_iff_remaining_after_23 :
    OddFourCarlet ↔
      (∀ (n : ℕ), Odd n → 7 ≤ n →
        ¬ 23 ∣ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K 4) := by
  constructor
  · intro h n hn hbound _ K _ _ _ hcard
    exact h n hn hbound K hcard
  · intro h n hn hbound K _ _ _ hcard
    classical
    by_cases h23 : 23 ∣ n
    · exact hasZeroSumSubspace_four_of_23_dvd_card n hcard h23
    exact h n hn hbound h23 K hcard

#print axioms oddFourCarlet_iff_remaining_after_23
end Carlet
