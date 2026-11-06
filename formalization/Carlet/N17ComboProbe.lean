import Carlet.N17N19InverseProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem c17Combo01 : c17V01 = c17V01 := by
  rfl
theorem c17Combo02 : c17V02 = c17V02 := by
  rfl
theorem c17Combo03 : c17V03 = c17V01 + c17V02 := by
  unfold c17V03 c17V01 c17V02
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo04 : c17V04 = c17V04 := by
  rfl
theorem c17Combo05 : c17V05 = c17V01 + c17V04 := by
  unfold c17V05 c17V01 c17V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo06 : c17V06 = c17V02 + c17V04 := by
  unfold c17V06 c17V02 c17V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo07 : c17V07 = c17V01 + c17V02 + c17V04 := by
  unfold c17V07 c17V01 c17V02 c17V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo08 : c17V08 = c17V08 := by
  rfl
theorem c17Combo09 : c17V09 = c17V01 + c17V08 := by
  unfold c17V09 c17V01 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo10 : c17V10 = c17V02 + c17V08 := by
  unfold c17V10 c17V02 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo11 : c17V11 = c17V01 + c17V02 + c17V08 := by
  unfold c17V11 c17V01 c17V02 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo12 : c17V12 = c17V04 + c17V08 := by
  unfold c17V12 c17V04 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo13 : c17V13 = c17V01 + c17V04 + c17V08 := by
  unfold c17V13 c17V01 c17V04 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo14 : c17V14 = c17V02 + c17V04 + c17V08 := by
  unfold c17V14 c17V02 c17V04 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo15 : c17V15 = c17V01 + c17V02 + c17V04 + c17V08 := by
  unfold c17V15 c17V01 c17V02 c17V04 c17V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo16 : c17V16 = c17V16 := by
  rfl
theorem c17Combo17 : c17V17 = c17V01 + c17V16 := by
  unfold c17V17 c17V01 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo18 : c17V18 = c17V02 + c17V16 := by
  unfold c17V18 c17V02 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo19 : c17V19 = c17V01 + c17V02 + c17V16 := by
  unfold c17V19 c17V01 c17V02 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo20 : c17V20 = c17V04 + c17V16 := by
  unfold c17V20 c17V04 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo21 : c17V21 = c17V01 + c17V04 + c17V16 := by
  unfold c17V21 c17V01 c17V04 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo22 : c17V22 = c17V02 + c17V04 + c17V16 := by
  unfold c17V22 c17V02 c17V04 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo23 : c17V23 = c17V01 + c17V02 + c17V04 + c17V16 := by
  unfold c17V23 c17V01 c17V02 c17V04 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo24 : c17V24 = c17V08 + c17V16 := by
  unfold c17V24 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo25 : c17V25 = c17V01 + c17V08 + c17V16 := by
  unfold c17V25 c17V01 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo26 : c17V26 = c17V02 + c17V08 + c17V16 := by
  unfold c17V26 c17V02 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo27 : c17V27 = c17V01 + c17V02 + c17V08 + c17V16 := by
  unfold c17V27 c17V01 c17V02 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo28 : c17V28 = c17V04 + c17V08 + c17V16 := by
  unfold c17V28 c17V04 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo29 : c17V29 = c17V01 + c17V04 + c17V08 + c17V16 := by
  unfold c17V29 c17V01 c17V04 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo30 : c17V30 = c17V02 + c17V04 + c17V08 + c17V16 := by
  unfold c17V30 c17V02 c17V04 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c17Combo31 : c17V31 = c17V01 + c17V02 + c17V04 + c17V08 + c17V16 := by
  unfold c17V31 c17V01 c17V02 c17V04 c17V08 c17V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
#print axioms c17Combo01
#print axioms c17Combo31



