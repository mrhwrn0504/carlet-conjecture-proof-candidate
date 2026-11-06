import Carlet.K4PrimeFrom29Probe
import Carlet.N29FourASBridgeProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

def OddFourPrimesFrom31 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 31 ≤ p → ∀ (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod 2) K], Fintype.card K = 2^p → HasZeroSumSubspace K 4

/-- The full odd k=4 problem is equivalent to its prime-degree cases from 31;
    the missing prime 29 is closed by an explicit unconditional construction. -/
theorem oddFourAll_iff_prime_degrees_from_31 :
    OddFourAll ↔ OddFourPrimesFrom31 := by
  constructor
  · intro hall p hp hp31 K _ _ _ hc
    have h29 := (oddFourAll_iff_prime_degrees_from_29.mp hall) p hp (by omega) K hc
    exact h29
  · intro hlarge
    apply (oddFourAll_iff_prime_degrees_from_29).mpr
    intro p hp hp29 K _ _ _ hc
    by_cases hp29eq : p = 29
    · subst p
      exact hasZeroSumSubspace_four_of_29_dvd_card 29 hc (by norm_num)
    · have hp31 : 31 ≤ p := by
        by_contra hlt
        have hrange : p = 29 ∨ p = 30 := by omega
        rcases hrange with h | h
        · exact (hp29eq h).elim
        · rw [h] at hp
          norm_num at hp
      exact hlarge p hp hp31 K hc

#print axioms oddFourAll_iff_prime_degrees_from_31
end Carlet
