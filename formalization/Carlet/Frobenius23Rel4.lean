import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def q23_18 : P17 := X^1 + X^7 + X^9 + X^13
lemma f23_rel_18 : r23_18^2 + r23_19 = f23*q23_18 := by
  unfold r23_18 r23_19 q23_18 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_19 : P17 := X^3 + X^9
lemma f23_rel_19 : r23_19^2 + r23_20 = f23*q23_19 := by
  unfold r23_19 r23_20 q23_19 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_20 : P17 := X^13
lemma f23_rel_20 : r23_20^2 + r23_21 = f23*q23_20 := by
  unfold r23_20 r23_21 q23_20 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_21 : P17 := X^3
lemma f23_rel_21 : r23_21^2 + r23_22 = f23*q23_21 := by
  unfold r23_21 r23_22 q23_21 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_22 : P17 := X^1
lemma f23_rel_22 : r23_22^2 + r23_23 = f23*q23_22 := by
  unfold r23_22 r23_23 q23_22 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f23_rel_18
#print axioms f23_rel_22
