import Carlet.N25FourASBridgeProbe
import Carlet.K4SmallOddRangeProbe
import Carlet.K4PrimeReductionArithmeticProbe
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet

def OddFourAll : Prop :=
  ∀ (n : ℕ), Odd n → 7 ≤ n → ∀ (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod 2) K], Fintype.card K = 2^n → HasZeroSumSubspace K 4

def OddFourPrimes : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 7 ≤ p → ∀ (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod 2) K], Fintype.card K = 2^p → HasZeroSumSubspace K 4

theorem k4_transfer_of_degree_divides (n d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2^n)
    (hsmall : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod 2) L],
      Fintype.card L = 2^d → HasZeroSumSubspace L 4) : HasZeroSumSubspace K 4 := by
  classical
  let L := GaloisField 2 d
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = d := GaloisField.finrank 2 (by omega)
  have hc : Fintype.card L = 2^d := by rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
  have hfin : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, finrank_eq_of_card n hcard] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := L) (L := K) hfin
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 4 (hsmall L hc)

theorem oddFourAll_iff_prime_degrees : OddFourAll ↔ OddFourPrimes := by
  constructor
  · intro h p hp hp7 K _ _ _ hc
    apply h p ?_ hp7 K hc
    have hp2 : p ≠ 2 := by omega
    exact Nat.odd_iff.mpr ((hp.eq_two_or_odd).resolve_left hp2)
  · intro h n hn hmin K _ _ _ hc
    by_cases h9 : 9 ∣ n
    · apply k4_transfer_of_degree_divides n 9 (by norm_num) h9 K hc
      intro L _ _ _ hcard
      exact k4_all_small_odd_degrees 9 (by norm_num) (by norm_num) (by norm_num) L hcard
    by_cases h15 : 15 ∣ n
    · apply k4_transfer_of_degree_divides n 15 (by norm_num) h15 K hc
      intro L _ _ _ hcard
      exact k4_all_small_odd_degrees 15 (by norm_num) (by norm_num) (by norm_num) L hcard
    by_cases h25 : 25 ∣ n
    · exact hasZeroSumSubspace_four_of_25_dvd_card n hc h25
    obtain ⟨p, hp, hp7, hpn⟩ := odd_degree_has_relevant_divisor n hn hmin h9 h15 h25
    apply k4_transfer_of_degree_divides n p (by omega) hpn K hc
    intro L _ _ _ hcard
    exact h p hp hp7 L hcard

#print axioms k4_transfer_of_degree_divides
#print axioms oddFourAll_iff_prime_degrees
end Carlet
