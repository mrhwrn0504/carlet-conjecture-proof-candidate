import Carlet.AdditiveClosure
import Carlet.ProbabilityEnergy

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

/-- A single high-dimensional entry point, combining the proved parity cases. -/
theorem hasZeroSumSubspace_high (n k : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hk : 10 ≤ k) (hbound : 2 * k + 1 ≤ n) :
    HasZeroSumSubspace K k := by
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨r, hr⟩ := heven
    have heq : k = 2 * (r - 1) + 2 := by omega
    rw [heq]
    exact hasZeroSumSubspace_of_high_even_dimension n (r - 1) hn (by omega) (by omega)
  · obtain ⟨r, hr⟩ := hodd
    have heq : k = 2 * r + 1 := by omega
    rw [heq]
    exact hasZeroSumSubspace_of_high_odd_dimension n r hn (by omega) (by omega)

/-- All lower-half dimensions reduce to the three small-dimensional families.
The base-family hypothesis is explicit; this is not a proof of those families. -/
theorem hasZeroSumSubspace_lowerHalf_of_small (n k : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hk : 3 ≤ k) (hbound : 2 * k + 1 ≤ n)
    (hbase : ∀ d : ℕ, 3 ≤ d → d ≤ 5 → 2 * d + 1 ≤ n → HasZeroSumSubspace K d) :
    HasZeroSumSubspace K k := by
  by_cases hhigh : 10 ≤ k
  · exact hasZeroSumSubspace_high n k hn hhigh hbound
  by_cases hsmall : k ≤ 5
  · exact hbase k hk hsmall hbound
  have h3 : HasZeroSumSubspace K 3 := hbase 3 (by omega) (by omega) (by omega)
  have h4 : HasZeroSumSubspace K 4 := hbase 4 (by omega) (by omega) (by omega)
  have h6 : HasZeroSumSubspace K 6 :=
    hasZeroSumSubspace_add n 3 3 hn (by omega) h3 h3
  have hcases : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact h6
  · exact hasZeroSumSubspace_add n 3 4 hn (by omega) h3 h4
  · exact hasZeroSumSubspace_add n 4 4 hn (by omega) h4 h4
  · exact hasZeroSumSubspace_add n 3 6 hn (by omega) h3 h6

/-- Exact reduction of the original conjecture to k=3,4,5 in the lower half.
All large dimensions, dimension addition and complementary symmetry are proved. -/
theorem oddCarletConjecture_iff_small_dimensions :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n → 3 ≤ k → k ≤ 5 → 2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk _ hbound K _ _ _ hcard
    exact h n k hn hk (by omega) K hcard
  · intro h n k hn hk hkn K _ _ _ hcard
    have hfin := finrank_eq_of_card (K := K) n hcard
    have hbase : ∀ d : ℕ, 3 ≤ d → d ≤ 5 → 2 * d + 1 ≤ n → HasZeroSumSubspace K d :=
      fun d hd hd5 hdn => h n d hn hd hd5 hdn K hcard
    by_cases hlow : 2 * k + 1 ≤ n
    · exact hasZeroSumSubspace_lowerHalf_of_small n k hfin hk hlow hbase
    · have hlow' : 2 * (n - k) + 1 ≤ n := by
        obtain ⟨r, hr⟩ := hn
        omega
      have hother := hasZeroSumSubspace_lowerHalf_of_small n (n - k) hfin
        (by omega) hlow' hbase
      exact (zeroSumSubspace_complement_of_card n k hcard (by omega) (by omega)).mpr hother

#print axioms hasZeroSumSubspace_high
#print axioms hasZeroSumSubspace_lowerHalf_of_small
#print axioms oddCarletConjecture_iff_small_dimensions

end Carlet
