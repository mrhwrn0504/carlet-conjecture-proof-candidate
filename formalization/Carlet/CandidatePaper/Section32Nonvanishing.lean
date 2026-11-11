import Carlet.CandidatePaper.RationalFunctionLogDerivative

/-!
An abstract form of the last-coordinate nonvanishing step in Section 3.2 of
the supplied candidate paper. Once the previous-dimensional reciprocal sum is
known to be a nonzero scalar in the coefficient field, adding the reciprocal
sum over any finite linear fiber cannot make it vanish.
-/

noncomputable section

namespace Carlet.CandidatePaper.Section32Nonvanishing

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem nonzero_constant_add_fiber_reciprocal_sum
    (s : Finset K) (c : K) (hc : c ≠ 0) :
    algebraMap K[X] (FractionRing K[X]) (C c) +
      ∑ a ∈ s,
        (algebraMap K[X] (FractionRing K[X]) (X + C a))⁻¹ ≠ 0 := by
  rw [Carlet.CandidatePaper.RationalFunctionLogDerivative.sum_inverse_linearFactors_eq_logDerivative]
  exact Carlet.CandidatePaper.RationalFunctionLogDerivative.scalar_add_logDerivative_ne_zero
    (Carlet.rootProduct s)
    (Carlet.CandidatePaper.RationalFunctionLogDerivative.rootProduct_monic s).ne_zero
    c hc

#print axioms nonzero_constant_add_fiber_reciprocal_sum

end Carlet.CandidatePaper.Section32Nonvanishing
