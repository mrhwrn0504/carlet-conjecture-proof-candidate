import Carlet.Frobenius29Base
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
def q29_15 : P17 := X^1 + X^7 + X^9 + X^13 + X^17 + X^21 + X^25
lemma f29_rel_15 : r29_15^2+r29_16=f29*q29_15 := by
  unfold r29_15 r29_16 q29_15 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_16 : P17 := 1 + X^1 + X^5 + X^9 + X^11 + X^13 + X^17 + X^21 + X^23 + X^25 + X^27
lemma f29_rel_16 : r29_16^2+r29_17=f29*q29_16 := by
  unfold r29_16 r29_17 q29_16 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_17 : P17 := 1 + X^1 + X^3 + X^5 + X^9 + X^13 + X^15 + X^23 + X^27
lemma f29_rel_17 : r29_17^2+r29_18=f29*q29_17 := by
  unfold r29_17 r29_18 q29_17 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_18 : P17 := 1 + X^5 + X^7 + X^17 + X^21 + X^25 + X^27
lemma f29_rel_18 : r29_18^2+r29_19=f29*q29_18 := by
  unfold r29_18 r29_19 q29_18 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_19 : P17 := 1 + X^5 + X^7 + X^9 + X^11 + X^13 + X^15 + X^17 + X^19 + X^21 + X^23 + X^27
lemma f29_rel_19 : r29_19^2+r29_20=f29*q29_19 := by
  unfold r29_19 r29_20 q29_19 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
