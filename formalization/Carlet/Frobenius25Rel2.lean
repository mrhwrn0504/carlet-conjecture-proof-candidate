import Carlet.Frobenius25Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def q25_6 : P17 := X^3 + X^15
lemma f25_rel_6 : r25_6^2 + r25_7 = f25*q25_6 := by
  unfold r25_6 r25_7 q25_6 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_7 : P17 := X^5 + X^11
lemma f25_rel_7 : r25_7^2 + r25_8 = f25*q25_7 := by
  unfold r25_7 r25_8 q25_7 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_8 : P17 := X^3
lemma f25_rel_8 : r25_8^2 + r25_9 = f25*q25_8 := by
  unfold r25_8 r25_9 q25_8 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_9 : P17 := X^1 + X^7 + X^19 + X^23
lemma f25_rel_9 : r25_9^2 + r25_10 = f25*q25_9 := by
  unfold r25_9 r25_10 q25_9 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_10 : P17 := X^1 + X^13 + X^15 + X^19 + X^21 + X^23
lemma f25_rel_10 : r25_10^2 + r25_11 = f25*q25_10 := by
  unfold r25_10 r25_11 q25_10 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_11 : P17 := X^1 + X^3 + X^5 + X^7 + X^11 + X^13 + X^15 + X^17 + X^19 + X^21
lemma f25_rel_11 : r25_11^2 + r25_12 = f25*q25_11 := by
  unfold r25_11 r25_12 q25_11 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f25_rel_6
#print axioms f25_rel_11
