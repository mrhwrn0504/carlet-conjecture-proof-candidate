import Carlet.Frobenius25Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def q25_12 : P17 := X^1 + X^3 + X^5 + X^9 + X^11 + X^13 + X^15 + X^17 + X^19
lemma f25_rel_12 : r25_12^2 + r25_13 = f25*q25_12 := by
  unfold r25_12 r25_13 q25_12 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_13 : P17 := X^1 + X^5 + X^7 + X^9 + X^11 + X^13
lemma f25_rel_13 : r25_13^2 + r25_14 = f25*q25_13 := by
  unfold r25_13 r25_14 q25_13 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_14 : P17 := X^1 + X^3 + X^11 + X^15 + X^19
lemma f25_rel_14 : r25_14^2 + r25_15 = f25*q25_14 := by
  unfold r25_14 r25_15 q25_14 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_15 : P17 := X^1 + X^5 + X^7 + X^13 + X^23
lemma f25_rel_15 : r25_15^2 + r25_16 = f25*q25_15 := by
  unfold r25_15 r25_16 q25_15 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_16 : P17 := X^7 + X^15 + X^19 + X^21 + X^23
lemma f25_rel_16 : r25_16^2 + r25_17 = f25*q25_16 := by
  unfold r25_16 r25_17 q25_16 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_17 : P17 := X^3 + X^5 + X^7 + X^11 + X^13 + X^15 + X^17 + X^19 + X^21
lemma f25_rel_17 : r25_17^2 + r25_18 = f25*q25_17 := by
  unfold r25_17 r25_18 q25_17 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f25_rel_12
#print axioms f25_rel_17
