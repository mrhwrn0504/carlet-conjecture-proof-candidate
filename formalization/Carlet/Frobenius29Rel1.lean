import Carlet.Frobenius29Base
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
def q29_0 : P17 := 0
lemma f29_rel_0 : r29_0^2+r29_1=f29*q29_0 := by
  unfold r29_0 r29_1 q29_0 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_1 : P17 := 0
lemma f29_rel_1 : r29_1^2+r29_2=f29*q29_1 := by
  unfold r29_1 r29_2 q29_1 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_2 : P17 := 0
lemma f29_rel_2 : r29_2^2+r29_3=f29*q29_2 := by
  unfold r29_2 r29_3 q29_2 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_3 : P17 := 0
lemma f29_rel_3 : r29_3^2+r29_4=f29*q29_3 := by
  unfold r29_3 r29_4 q29_3 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q29_4 : P17 := X^3
lemma f29_rel_4 : r29_4^2+r29_5=f29*q29_4 := by
  unfold r29_4 r29_5 q29_4 f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
