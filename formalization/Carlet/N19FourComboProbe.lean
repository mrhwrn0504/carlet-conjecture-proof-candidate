import Carlet.N19FourInverseProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem e19Combo01 : e19V01 = e19V01 := by
  rfl
theorem e19Combo02 : e19V02 = e19V02 := by
  rfl
theorem e19Combo03 : e19V03 = e19V01 + e19V02 := by
  unfold e19V03 e19V01 e19V02
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo04 : e19V04 = e19V04 := by
  rfl
theorem e19Combo05 : e19V05 = e19V01 + e19V04 := by
  unfold e19V05 e19V01 e19V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo06 : e19V06 = e19V02 + e19V04 := by
  unfold e19V06 e19V02 e19V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo07 : e19V07 = e19V01 + e19V02 + e19V04 := by
  unfold e19V07 e19V01 e19V02 e19V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo08 : e19V08 = e19V08 := by
  rfl
theorem e19Combo09 : e19V09 = e19V01 + e19V08 := by
  unfold e19V09 e19V01 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo10 : e19V10 = e19V02 + e19V08 := by
  unfold e19V10 e19V02 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo11 : e19V11 = e19V01 + e19V02 + e19V08 := by
  unfold e19V11 e19V01 e19V02 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo12 : e19V12 = e19V04 + e19V08 := by
  unfold e19V12 e19V04 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo13 : e19V13 = e19V01 + e19V04 + e19V08 := by
  unfold e19V13 e19V01 e19V04 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo14 : e19V14 = e19V02 + e19V04 + e19V08 := by
  unfold e19V14 e19V02 e19V04 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e19Combo15 : e19V15 = e19V01 + e19V02 + e19V04 + e19V08 := by
  unfold e19V15 e19V01 e19V02 e19V04 e19V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
