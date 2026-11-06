import Carlet.Frobenius29Base
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
def q29_20 : P17 := 1 + X^7 + X^19 + X^21 + X^25 + X^27
lemma f29_rel_20 : r29_20^2+r29_21=f29*q29_20 := by
  unfold r29_20 r29_21 q29_20 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_21 : P17 := X^9 + X^11 + X^17 + X^21
lemma f29_rel_21 : r29_21^2+r29_22=f29*q29_21 := by
  unfold r29_21 r29_22 q29_21 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_22 : P17 := X^5 + X^7 + X^9 + X^11 + X^13 + X^17
lemma f29_rel_22 : r29_22^2+r29_23=f29*q29_22 := by
  unfold r29_22 r29_23 q29_22 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_23 : P17 := 1 + X^1 + X^3 + X^5 + X^7 + X^9 + X^23 + X^27
lemma f29_rel_23 : r29_23^2+r29_24=f29*q29_23 := by
  unfold r29_23 r29_24 q29_23 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_24 : P17 := X^3 + X^17 + X^21 + X^25
lemma f29_rel_24 : r29_24^2+r29_25=f29*q29_24 := by
  unfold r29_24 r29_25 q29_24 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
