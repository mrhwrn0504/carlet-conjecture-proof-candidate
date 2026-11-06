import Carlet.N11FourInverseProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem e11Combo01 : e11V01 = e11V01 := by
  rfl
theorem e11Combo02 : e11V02 = e11V02 := by
  rfl
theorem e11Combo03 : e11V03 = e11V01 + e11V02 := by
  unfold e11V03 e11V01 e11V02
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo04 : e11V04 = e11V04 := by
  rfl
theorem e11Combo05 : e11V05 = e11V01 + e11V04 := by
  unfold e11V05 e11V01 e11V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo06 : e11V06 = e11V02 + e11V04 := by
  unfold e11V06 e11V02 e11V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo07 : e11V07 = e11V01 + e11V02 + e11V04 := by
  unfold e11V07 e11V01 e11V02 e11V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo08 : e11V08 = e11V08 := by
  rfl
theorem e11Combo09 : e11V09 = e11V01 + e11V08 := by
  unfold e11V09 e11V01 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo10 : e11V10 = e11V02 + e11V08 := by
  unfold e11V10 e11V02 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo11 : e11V11 = e11V01 + e11V02 + e11V08 := by
  unfold e11V11 e11V01 e11V02 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo12 : e11V12 = e11V04 + e11V08 := by
  unfold e11V12 e11V04 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo13 : e11V13 = e11V01 + e11V04 + e11V08 := by
  unfold e11V13 e11V01 e11V04 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo14 : e11V14 = e11V02 + e11V04 + e11V08 := by
  unfold e11V14 e11V02 e11V04 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem e11Combo15 : e11V15 = e11V01 + e11V02 + e11V04 + e11V08 := by
  unfold e11V15 e11V01 e11V02 e11V04 e11V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
