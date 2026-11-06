import Carlet.N19ModulusBridgeProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem c19Combo01 : c19V01 = c19V01 := by
  rfl
theorem c19Combo02 : c19V02 = c19V02 := by
  rfl
theorem c19Combo03 : c19V03 = c19V01 + c19V02 := by
  unfold c19V03 c19V01 c19V02
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo04 : c19V04 = c19V04 := by
  rfl
theorem c19Combo05 : c19V05 = c19V01 + c19V04 := by
  unfold c19V05 c19V01 c19V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo06 : c19V06 = c19V02 + c19V04 := by
  unfold c19V06 c19V02 c19V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo07 : c19V07 = c19V01 + c19V02 + c19V04 := by
  unfold c19V07 c19V01 c19V02 c19V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo08 : c19V08 = c19V08 := by
  rfl
theorem c19Combo09 : c19V09 = c19V01 + c19V08 := by
  unfold c19V09 c19V01 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo10 : c19V10 = c19V02 + c19V08 := by
  unfold c19V10 c19V02 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo11 : c19V11 = c19V01 + c19V02 + c19V08 := by
  unfold c19V11 c19V01 c19V02 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo12 : c19V12 = c19V04 + c19V08 := by
  unfold c19V12 c19V04 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo13 : c19V13 = c19V01 + c19V04 + c19V08 := by
  unfold c19V13 c19V01 c19V04 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo14 : c19V14 = c19V02 + c19V04 + c19V08 := by
  unfold c19V14 c19V02 c19V04 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo15 : c19V15 = c19V01 + c19V02 + c19V04 + c19V08 := by
  unfold c19V15 c19V01 c19V02 c19V04 c19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo16 : c19V16 = c19V16 := by
  rfl
theorem c19Combo17 : c19V17 = c19V01 + c19V16 := by
  unfold c19V17 c19V01 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo18 : c19V18 = c19V02 + c19V16 := by
  unfold c19V18 c19V02 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo19 : c19V19 = c19V01 + c19V02 + c19V16 := by
  unfold c19V19 c19V01 c19V02 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo20 : c19V20 = c19V04 + c19V16 := by
  unfold c19V20 c19V04 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo21 : c19V21 = c19V01 + c19V04 + c19V16 := by
  unfold c19V21 c19V01 c19V04 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo22 : c19V22 = c19V02 + c19V04 + c19V16 := by
  unfold c19V22 c19V02 c19V04 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo23 : c19V23 = c19V01 + c19V02 + c19V04 + c19V16 := by
  unfold c19V23 c19V01 c19V02 c19V04 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo24 : c19V24 = c19V08 + c19V16 := by
  unfold c19V24 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo25 : c19V25 = c19V01 + c19V08 + c19V16 := by
  unfold c19V25 c19V01 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo26 : c19V26 = c19V02 + c19V08 + c19V16 := by
  unfold c19V26 c19V02 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo27 : c19V27 = c19V01 + c19V02 + c19V08 + c19V16 := by
  unfold c19V27 c19V01 c19V02 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo28 : c19V28 = c19V04 + c19V08 + c19V16 := by
  unfold c19V28 c19V04 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo29 : c19V29 = c19V01 + c19V04 + c19V08 + c19V16 := by
  unfold c19V29 c19V01 c19V04 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo30 : c19V30 = c19V02 + c19V04 + c19V08 + c19V16 := by
  unfold c19V30 c19V02 c19V04 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem c19Combo31 : c19V31 = c19V01 + c19V02 + c19V04 + c19V08 + c19V16 := by
  unfold c19V31 c19V01 c19V02 c19V04 c19V08 c19V16
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
#print axioms c19Combo01
#print axioms c19Combo31



