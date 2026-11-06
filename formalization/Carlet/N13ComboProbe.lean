import Carlet.N13InverseProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem cert13Combo01 : cert13V01 = cert13V01 := by
  rfl
theorem cert13Combo02 : cert13V02 = cert13V02 := by
  rfl
theorem cert13Combo03 : cert13V03 = cert13V01 + cert13V02 := by
  unfold cert13V03 cert13V01 cert13V02
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo04 : cert13V04 = cert13V04 := by
  rfl
theorem cert13Combo05 : cert13V05 = cert13V01 + cert13V04 := by
  unfold cert13V05 cert13V01 cert13V04
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo06 : cert13V06 = cert13V02 + cert13V04 := by
  unfold cert13V06 cert13V02 cert13V04
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo07 : cert13V07 = cert13V01 + cert13V02 + cert13V04 := by
  unfold cert13V07 cert13V01 cert13V02 cert13V04
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo08 : cert13V08 = cert13V08 := by
  rfl
theorem cert13Combo09 : cert13V09 = cert13V01 + cert13V08 := by
  unfold cert13V09 cert13V01 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo10 : cert13V10 = cert13V02 + cert13V08 := by
  unfold cert13V10 cert13V02 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo11 : cert13V11 = cert13V01 + cert13V02 + cert13V08 := by
  unfold cert13V11 cert13V01 cert13V02 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo12 : cert13V12 = cert13V04 + cert13V08 := by
  unfold cert13V12 cert13V04 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo13 : cert13V13 = cert13V01 + cert13V04 + cert13V08 := by
  unfold cert13V13 cert13V01 cert13V04 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo14 : cert13V14 = cert13V02 + cert13V04 + cert13V08 := by
  unfold cert13V14 cert13V02 cert13V04 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo15 : cert13V15 = cert13V01 + cert13V02 + cert13V04 + cert13V08 := by
  unfold cert13V15 cert13V01 cert13V02 cert13V04 cert13V08
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo16 : cert13V16 = cert13V16 := by
  rfl
theorem cert13Combo17 : cert13V17 = cert13V01 + cert13V16 := by
  unfold cert13V17 cert13V01 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo18 : cert13V18 = cert13V02 + cert13V16 := by
  unfold cert13V18 cert13V02 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo19 : cert13V19 = cert13V01 + cert13V02 + cert13V16 := by
  unfold cert13V19 cert13V01 cert13V02 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo20 : cert13V20 = cert13V04 + cert13V16 := by
  unfold cert13V20 cert13V04 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo21 : cert13V21 = cert13V01 + cert13V04 + cert13V16 := by
  unfold cert13V21 cert13V01 cert13V04 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo22 : cert13V22 = cert13V02 + cert13V04 + cert13V16 := by
  unfold cert13V22 cert13V02 cert13V04 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo23 : cert13V23 = cert13V01 + cert13V02 + cert13V04 + cert13V16 := by
  unfold cert13V23 cert13V01 cert13V02 cert13V04 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo24 : cert13V24 = cert13V08 + cert13V16 := by
  unfold cert13V24 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo25 : cert13V25 = cert13V01 + cert13V08 + cert13V16 := by
  unfold cert13V25 cert13V01 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo26 : cert13V26 = cert13V02 + cert13V08 + cert13V16 := by
  unfold cert13V26 cert13V02 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo27 : cert13V27 = cert13V01 + cert13V02 + cert13V08 + cert13V16 := by
  unfold cert13V27 cert13V01 cert13V02 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo28 : cert13V28 = cert13V04 + cert13V08 + cert13V16 := by
  unfold cert13V28 cert13V04 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo29 : cert13V29 = cert13V01 + cert13V04 + cert13V08 + cert13V16 := by
  unfold cert13V29 cert13V01 cert13V04 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo30 : cert13V30 = cert13V02 + cert13V04 + cert13V08 + cert13V16 := by
  unfold cert13V30 cert13V02 cert13V04 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem cert13Combo31 : cert13V31 = cert13V01 + cert13V02 + cert13V04 + cert13V08 + cert13V16 := by
  unfold cert13V31 cert13V01 cert13V02 cert13V04 cert13V08 cert13V16
  ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
#print axioms cert13Combo01
#print axioms cert13Combo31



