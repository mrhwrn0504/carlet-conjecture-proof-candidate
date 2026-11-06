import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def q23_0 : P17 := 0
lemma f23_rel_0 : r23_0^2 + r23_1 = f23*q23_0 := by
  unfold r23_0 r23_1 q23_0 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_1 : P17 := 0
lemma f23_rel_1 : r23_1^2 + r23_2 = f23*q23_1 := by
  unfold r23_1 r23_2 q23_1 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_2 : P17 := 0
lemma f23_rel_2 : r23_2^2 + r23_3 = f23*q23_2 := by
  unfold r23_2 r23_3 q23_2 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_3 : P17 := 0
lemma f23_rel_3 : r23_3^2 + r23_4 = f23*q23_3 := by
  unfold r23_3 r23_4 q23_3 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_4 : P17 := X^9
lemma f23_rel_4 : r23_4^2 + r23_5 = f23*q23_4 := by
  unfold r23_4 r23_5 q23_4 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def q23_5 : P17 := X^5
lemma f23_rel_5 : r23_5^2 + r23_6 = f23*q23_5 := by
  unfold r23_5 r23_6 q23_5 f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms f23_rel_0
#print axioms f23_rel_5
