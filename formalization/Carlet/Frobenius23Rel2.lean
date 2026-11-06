import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def q23_6 : P17 := X^13
lemma f23_rel_6 : r23_6^2 + r23_7 = f23*q23_6 := by
  unfold r23_6 r23_7 q23_6 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_7 : P17 := X^3 + X^13 + X^17
lemma f23_rel_7 : r23_7^2 + r23_8 = f23*q23_7 := by
  unfold r23_7 r23_8 q23_7 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_8 : P17 := X^11 + X^13 + X^17 + X^21
lemma f23_rel_8 : r23_8^2 + r23_9 = f23*q23_8 := by
  unfold r23_8 r23_9 q23_8 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_9 : P17 := X^1 + X^11 + X^13 + X^19 + X^21
lemma f23_rel_9 : r23_9^2 + r23_10 = f23*q23_9 := by
  unfold r23_9 r23_10 q23_9 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_10 : P17 := X^9 + X^13 + X^15 + X^19 + X^21
lemma f23_rel_10 : r23_10^2 + r23_11 = f23*q23_10 := by
  unfold r23_10 r23_11 q23_10 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_11 : P17 := X^5 + X^7 + X^13 + X^15 + X^17 + X^19 + X^21
lemma f23_rel_11 : r23_11^2 + r23_12 = f23*q23_11 := by
  unfold r23_11 r23_12 q23_11 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f23_rel_6
#print axioms f23_rel_11
