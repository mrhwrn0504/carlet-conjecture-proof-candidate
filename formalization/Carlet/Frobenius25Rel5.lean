import Carlet.Frobenius25Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def q25_24 : P17 := X^1
lemma f25_rel_24 : r25_24^2 + r25_25 = f25*q25_24 := by
  unfold r25_24 r25_25 q25_24 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f25_rel_24
#print axioms f25_rel_24
