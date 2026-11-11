import Carlet.FrobeniusCoefficients

/-!
The derivative of a Frobenius-supported polynomial in characteristic two is
its linear coefficient. This is the derivative step used for the fiber
polynomial in the candidate paper's Section 3.2.
-/

noncomputable section

open Polynomial

namespace Carlet.CandidatePaper.Section32SubspaceDerivative

variable {K : Type*} [Field K] [CharP K 2]

/-- A polynomial supported on powers of two has constant derivative, equal to
its coefficient of `X`. -/
theorem derivative_eq_C_coeff_one_of_frobeniusSupported
    (p : K[X]) (hs : FrobeniusSupported p) :
    p.derivative = C (p.coeff 1) := by
  ext n
  rw [Polynomial.coeff_derivative, Polynomial.coeff_C]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [if_neg hn]
    by_cases hp : p.coeff (n + 1) = 0
    · simp [hp]
    · obtain ⟨j, hj⟩ := hs (n + 1) hp
      by_cases hj0 : j = 0
      · subst j
        simp at hj
        omega
      · have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have hpow : (2 : K) ^ j = 0 := by
          rw [htwo]
          exact zero_pow (Nat.ne_of_gt (Nat.pos_of_ne_zero hj0))
        have hsum : ((n + 1 : ℕ) : K) = 0 := by
          calc
            ((n + 1 : ℕ) : K) = ((2 ^ j : ℕ) : K) := by rw [hj]
            _ = (2 : K) ^ j := by norm_cast
            _ = 0 := hpow
        have hfac : (n : K) + 1 = 0 := by
          simpa [Nat.cast_add, Nat.cast_one] using hsum
        simp [hfac]

#print axioms derivative_eq_C_coeff_one_of_frobeniusSupported

end Carlet.CandidatePaper.Section32SubspaceDerivative
