import Carlet.Frobenius29Base
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
def q29_25 : P17 := X^5 + X^9 + X^11 + X^13 + X^15 + X^17 + X^21 + X^25
lemma f29_rel_25 : r29_25^2+r29_26=f29*q29_25 := by
  unfold r29_25 r29_26 q29_25 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_26 : P17 := X^9 + X^13 + X^17 + X^21 + X^25
lemma f29_rel_26 : r29_26^2+r29_27=f29*q29_26 := by
  unfold r29_26 r29_27 q29_26 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_27 : P17 := X^1 + X^3 + X^5 + X^7 + X^9 + X^11 + X^13 + X^17 + X^21 + X^25
lemma f29_rel_27 : r29_27^2+r29_28=f29*q29_27 := by
  unfold r29_27 r29_28 q29_27 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_28 : P17 := 1 + X^1 + X^3 + X^5 + X^7 + X^9 + X^11 + X^13 + X^15 + X^17 + X^19 + X^21 + X^23 + X^25 + X^27
lemma f29_rel_28 : r29_28^2+r29_29=f29*q29_28 := by
  unfold r29_28 r29_29 q29_28 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
