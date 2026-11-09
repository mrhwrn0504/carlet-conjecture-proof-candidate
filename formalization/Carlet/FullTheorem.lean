import Carlet.MainTheorem
import Carlet.EvenDegree
import Mathlib.Tactic

noncomputable section

namespace Carlet

/-- The full parity-sensitive finite-field form of Carlet's conjecture.

For even n, every dimension 2 ≤ k ≤ n-2 occurs. For odd n, every
dimension 3 ≤ k ≤ n-3 occurs. The theorem is uniform over all finite
fields of characteristic two and cardinality 2^n. -/
theorem carletConjecture_full
    (n k : ℕ)
    (hcase : (Even n ∧ 2 ≤ k ∧ k + 2 ≤ n) ∨
      (Odd n ∧ 3 ≤ k ∧ k + 3 ≤ n))
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [DecidableEq K] (hcard : Fintype.card K = 2 ^ n) :
    HasZeroSumSubspace K k := by
  rcases hcase with hEvenCase | hOddCase
  · exact evenDegreeCarlet_unconditional n hEvenCase.1 K hcard k
      hEvenCase.2.1 hEvenCase.2.2
  · exact oddCarletConjecture_main n k hOddCase.1
      hOddCase.2.1 hOddCase.2.2 K hcard

/-- The common n ≥ 6, 3 ≤ k ≤ n-3 formulation used in the recent
counting proof follows as an immediate specialization. -/
theorem carletConjecture_n_ge6
    (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) (hkn : k + 3 ≤ n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [DecidableEq K] (hcard : Fintype.card K = 2 ^ n) :
    HasZeroSumSubspace K k := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · exact evenDegreeCarlet_unconditional n hEven K hcard k (by omega) (by omega)
  · exact oddCarletConjecture_main n k hOdd hk (by omega) K hcard

#print axioms carletConjecture_full
#print axioms carletConjecture_n_ge6

end Carlet