import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def q23_12 : P17 := X^7 + X^11 + X^15 + X^17 + X^19 + X^21
lemma f23_rel_12 : r23_12^2 + r23_13 = f23*q23_12 := by
  unfold r23_12 r23_13 q23_12 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_13 : P17 := X^3 + X^5 + X^7 + X^9 + X^11 + X^15 + X^19 + X^21
lemma f23_rel_13 : r23_13^2 + r23_14 = f23*q23_13 := by
  unfold r23_13 r23_14 q23_13 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_14 : P17 := X^3 + X^7 + X^15 + X^19 + X^21
lemma f23_rel_14 : r23_14^2 + r23_15 = f23*q23_14 := by
  unfold r23_14 r23_15 q23_14 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_15 : P17 := X^3 + X^5 + X^7 + X^9 + X^13 + X^15 + X^19 + X^21
lemma f23_rel_15 : r23_15^2 + r23_16 = f23*q23_15 := by
  unfold r23_15 r23_16 q23_15 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_16 : P17 := X^1 + X^3 + X^7 + X^9 + X^13 + X^15 + X^19
lemma f23_rel_16 : r23_16^2 + r23_17 = f23*q23_16 := by
  unfold r23_16 r23_17 q23_16 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_17 : P17 := X^3 + X^7 + X^9 + X^15
lemma f23_rel_17 : r23_17^2 + r23_18 = f23*q23_17 := by
  unfold r23_17 r23_18 q23_17 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f23_rel_12
#print axioms f23_rel_17
