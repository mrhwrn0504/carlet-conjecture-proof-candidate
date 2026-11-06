import Carlet.N9K5SubfieldProbe
import Carlet.SubfieldFive
import Carlet.RemainingCases19
import Mathlib.Tactic

noncomputable section
namespace Carlet

/-- All admissible odd degrees below 20 are already covered by the
    degree-9/11/13/17/19 constructions or by the 5-subfield construction
    at degree 15. This is the finite edge of the general k=5 theorem. -/
theorem hasZeroSumSubspace_five_of_odd_card_lt20
    (n : ℕ) (hn : Odd n) (hmin : 9 ≤ n) (hmax : n < 20)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2 ^ n) : HasZeroSumSubspace K 5 := by
  have hcases : n = 9 ∨ n = 11 ∨ n = 13 ∨ n = 15 ∨ n = 17 ∨ n = 19 := by
    rcases hn with ⟨m, hm⟩
    omega
  rcases hcases with h | h | h | h | h | h
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

#print axioms hasZeroSumSubspace_five_of_odd_card_lt20

end Carlet
