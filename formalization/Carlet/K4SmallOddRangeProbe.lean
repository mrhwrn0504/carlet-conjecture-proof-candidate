import Carlet.FourDimension7
import Carlet.N9K4CompleteProbe
import Carlet.N11FourK4CompleteProbe
import Carlet.N13K4FourCertificate
import Carlet.FourDimension15
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
namespace Carlet

theorem k4_all_small_odd_degrees (n : ℕ) (hn : Odd n) (hmin : 7 ≤ n) (hmax : n < 17)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2^n) : HasZeroSumSubspace K 4 := by
  classical
  have hc : n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 13 ∨ n = 15 := by
    rcases hn with ⟨m, hm⟩
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact hasZeroSumSubspace_four_of_seven_dvd 7 (finrank_eq_of_card 7 hcard) (by norm_num)
  · exact hasZeroSumSubspace_n9_four_card_probe hcard
  · exact hasZeroSumSubspace_n11_four_card_probe hcard
  · exact hasZeroSumSubspace_four_of_13_dvd_card 13 hcard (by norm_num)
  · exact hasZeroSumSubspace_four_of_15_dvd 15 (finrank_eq_of_card 15 hcard) (by norm_num)

#print axioms k4_all_small_odd_degrees
end Carlet
