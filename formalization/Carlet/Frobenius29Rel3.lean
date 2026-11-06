import Carlet.Frobenius29Base
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
def q29_10 : P17 := X^5 + X^17 + X^21
lemma f29_rel_10 : r29_10^2+r29_11=f29*q29_10 := by
  unfold r29_10 r29_11 q29_10 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_11 : P17 := X^5 + X^7 + X^9 + X^13 + X^15 + X^17 + X^23
lemma f29_rel_11 : r29_11^2+r29_12=f29*q29_11 := by
  unfold r29_11 r29_12 q29_11 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_12 : P17 := X^9 + X^17 + X^21
lemma f29_rel_12 : r29_12^2+r29_13=f29*q29_12 := by
  unfold r29_12 r29_13 q29_12 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_13 : P17 := 1 + X^5 + X^9 + X^11 + X^13 + X^15 + X^17 + X^23 + X^27
lemma f29_rel_13 : r29_13^2+r29_14=f29*q29_13 := by
  unfold r29_13 r29_14 q29_13 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_14 : P17 := X^7 + X^9 + X^11 + X^15 + X^17 + X^21 + X^25
lemma f29_rel_14 : r29_14^2+r29_15=f29*q29_14 := by
  unfold r29_14 r29_15 q29_14 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
