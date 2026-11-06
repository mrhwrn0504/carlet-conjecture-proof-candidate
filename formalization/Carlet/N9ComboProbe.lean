import Carlet.N9InverseProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem d9Combo01 : d9V01 = d9V01 := by
  rfl
theorem d9Combo02 : d9V02 = d9V02 := by
  rfl
theorem d9Combo03 : d9V03 = d9V01 + d9V02 := by
  unfold d9V03 d9V01 d9V02
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo04 : d9V04 = d9V04 := by
  rfl
theorem d9Combo05 : d9V05 = d9V01 + d9V04 := by
  unfold d9V05 d9V01 d9V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo06 : d9V06 = d9V02 + d9V04 := by
  unfold d9V06 d9V02 d9V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo07 : d9V07 = d9V01 + d9V02 + d9V04 := by
  unfold d9V07 d9V01 d9V02 d9V04
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo08 : d9V08 = d9V08 := by
  rfl
theorem d9Combo09 : d9V09 = d9V01 + d9V08 := by
  unfold d9V09 d9V01 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo10 : d9V10 = d9V02 + d9V08 := by
  unfold d9V10 d9V02 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo11 : d9V11 = d9V01 + d9V02 + d9V08 := by
  unfold d9V11 d9V01 d9V02 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo12 : d9V12 = d9V04 + d9V08 := by
  unfold d9V12 d9V04 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo13 : d9V13 = d9V01 + d9V04 + d9V08 := by
  unfold d9V13 d9V01 d9V04 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo14 : d9V14 = d9V02 + d9V04 + d9V08 := by
  unfold d9V14 d9V02 d9V04 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem d9Combo15 : d9V15 = d9V01 + d9V02 + d9V04 + d9V08 := by
  unfold d9V15 d9V01 d9V02 d9V04 d9V08
  ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
