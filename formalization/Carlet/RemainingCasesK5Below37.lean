import Carlet.N9K5SubfieldProbe
import Carlet.SubfieldFive
import Carlet.RemainingCases11
import Carlet.RemainingCases13
import Carlet.RemainingCases17
import Carlet.RemainingCases19
import Carlet.RemainingCases29K5Probe
import Carlet.FiveDimension21
import Carlet.FiveDimension31
import Mathlib.Tactic

noncomputable section
namespace Carlet

/-- Every admissible odd degree below 37 already has a checked k=5
    construction: six small direct degrees, the degree-23 certificate, and
    the existing 5-, 9-, 11-, 21-, 29-, and 31-divisible families. -/
theorem hasZeroSumSubspace_five_of_odd_card_lt37
    (n : ℕ) (hn : Odd n) (hmin : 9 ≤ n) (hmax : n < 37)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2 ^ n) : HasZeroSumSubspace K 5 := by
  classical
  have hcases :
      n = 9 ∨ n = 11 ∨ n = 13 ∨ n = 15 ∨ n = 17 ∨ n = 19 ∨
      n = 21 ∨ n = 23 ∨ n = 25 ∨ n = 27 ∨ n = 29 ∨ n = 31 ∨
      n = 33 ∨ n = 35 := by
    rcases hn with ⟨m, hm⟩
    omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact hasZeroSumSubspace_five_of_9_dvd 9
      (finrank_eq_of_card 9 hcard) (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_11_dvd_card 11 hcard (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_13_dvd_card 13 hcard (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_dvd 15
      (finrank_eq_of_card 15 hcard) (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_17_dvd_card 17 hcard (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_19_dvd_card 19 hcard (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_21_dvd 21
      (finrank_eq_of_card 21 hcard) (by norm_num)
  · subst n
    exact hasZeroSumSubspace_n23_card_probe hcard
  · subst n
    exact hasZeroSumSubspace_five_of_dvd 25
      (finrank_eq_of_card 25 hcard) (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_9_dvd 27
      (finrank_eq_of_card 27 hcard) (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_29_dvd_card 29 hcard (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_31_dvd 31
      (finrank_eq_of_card 31 hcard) (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_11_dvd_card 33 hcard (by norm_num)
  · subst n
    exact hasZeroSumSubspace_five_of_dvd 35
      (finrank_eq_of_card 35 hcard) (by norm_num)

#print axioms hasZeroSumSubspace_five_of_odd_card_lt37

end Carlet
