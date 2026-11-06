import Carlet.Frobenius23Chain12
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
lemma f23_bezout : (1:P17)*f23 +
    (X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^11 + X^12 + X^13 +
     X^14 + X^15 + X^16 + X^17 + X^18 + X^19 + X^20 + X^21)*((X:P17)^2+X) = 1 := by
  unfold f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17,
    c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17,
    c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem f23_dvd_frobPoly_sub : f23 ∣ frobPoly 23 - X := by
  have h := f23_dvd_frob_plus_23
  have hneg : -(X:P17) = X := by
    have hx : (X:P17) + X = 0 := by
      have ht := congrArg (fun z:P17 => z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  simpa [r23_23, sub_eq_add_neg, hneg] using h
#print axioms f23_dvd_frobPoly_sub
