import Carlet.K4PrimeDegreeReductionProbe
import Carlet.N17FourK4CompleteProbe
import Carlet.N19FourK4CompleteProbe
import Carlet.N23FourASBridgeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet

def OddFourPrimesFrom29 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 29 ≤ p → ∀ (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod 2) K], Fintype.card K = 2^p → HasZeroSumSubspace K 4

theorem oddFourAll_iff_prime_degrees_from_29 : OddFourAll ↔ OddFourPrimesFrom29 := by
  constructor
  · intro hall p hp hp29 K _ _ _ hc
    apply hall p ?_ (by omega) K hc
    have hp2 : p ≠ 2 := by omega
    exact Nat.odd_iff.mpr ((hp.eq_two_or_odd).resolve_left hp2)
  · intro hlarge
    apply oddFourAll_iff_prime_degrees.mpr
    intro p hp hp7 K _ _ _ hc
    by_cases h29 : 29 ≤ p
    · exact hlarge p hp h29 K hc
    have hsmall : p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
      have hmax : p ≤ 28 := by omega
      interval_cases p <;> norm_num at *
    rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl
    · exact k4_all_small_odd_degrees 7 (by norm_num) (by norm_num) (by norm_num) K hc
    · exact k4_all_small_odd_degrees 11 (by norm_num) (by norm_num) (by norm_num) K hc
    · exact k4_all_small_odd_degrees 13 (by norm_num) (by norm_num) (by norm_num) K hc
    · exact hasZeroSumSubspace_n17_four_card_probe hc
    · exact hasZeroSumSubspace_n19_four_card_probe hc
    · exact hasZeroSumSubspace_four_of_23_dvd_card 23 hc (by norm_num)

#print axioms oddFourAll_iff_prime_degrees_from_29
end Carlet
