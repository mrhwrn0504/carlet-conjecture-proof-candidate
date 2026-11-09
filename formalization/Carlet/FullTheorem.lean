import Carlet.MainTheorem
import Carlet.EvenDegree
import Mathlib.Tactic

noncomputable section

namespace Carlet

/-- The full finite-field form of Carlet's zero-sum subspace conjecture:
for every finite field of characteristic two and cardinality 2^n, every
admissible dimension 3 ≤ k ≤ n-3 has a k-dimensional zero-sum subspace.

The proof combines the independently formalized odd-degree theorem with the
even-degree theorem. The even-degree theorem is stronger at its lower edge:
it allows k ≥ 2 and k+2 ≤ n. -/
theorem carletConjecture_full
    (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) (hkn : k + 3 ≤ n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [DecidableEq K] (hcard : Fintype.card K = 2 ^ n) :
    HasZeroSumSubspace K k := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · exact evenDegreeCarlet_unconditional n hEven K hcard k hk (by omega)
  · exact oddCarletConjecture_main n k hOdd hk (by omega) K hcard

#print axioms carletConjecture_full

end Carlet
