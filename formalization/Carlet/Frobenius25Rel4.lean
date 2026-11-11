import Carlet.Frobenius25Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def q25_18 : P17 := X^1 + X^5 + X^7 + X^9 + X^11 + X^13 + X^15 + X^17 + X^19
lemma f25_rel_18 : r25_18^2 + r25_19 = f25*q25_18 := by
  unfold r25_18 r25_19 q25_18 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_19 : P17 := X^1 + X^5 + X^7 + X^9 + X^11 + X^13
lemma f25_rel_19 : r25_19^2 + r25_20 = f25*q25_19 := by
  unfold r25_19 r25_20 q25_19 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_20 : P17 := X^1 + X^7 + X^11 + X^19
lemma f25_rel_20 : r25_20^2 + r25_21 = f25*q25_20 := by
  unfold r25_20 r25_21 q25_20 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_21 : P17 := X^11 + X^13
lemma f25_rel_21 : r25_21^2 + r25_22 = f25*q25_21 := by
  unfold r25_21 r25_22 q25_21 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_22 : P17 := X^1 + X^19
lemma f25_rel_22 : r25_22^2 + r25_23 = f25*q25_22 := by
  unfold r25_22 r25_23 q25_22 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q25_23 : P17 := X^13
lemma f25_rel_23 : r25_23^2 + r25_24 = f25*q25_23 := by
  unfold r25_23 r25_24 q25_23 f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f25_rel_18
#print axioms f25_rel_23
