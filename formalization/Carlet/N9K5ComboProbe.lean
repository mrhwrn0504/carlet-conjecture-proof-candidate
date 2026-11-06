import Carlet.N9K5InverseProbe
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def n9K5BasePoly : Fin 5 → P17
| 0 => n9K5V01
| 1 => n9K5V02
| 2 => n9K5V04
| 3 => n9K5V08
| 4 => n9K5V16
theorem n9K5Combo01 : n9K5V01 = n9K5BasePoly 0 := by rfl
theorem n9K5Combo02 : n9K5V02 = n9K5BasePoly 1 := by rfl
theorem n9K5Combo03 : n9K5V03 = n9K5BasePoly 0 + n9K5BasePoly 1 := by
  simp [n9K5V03, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo04 : n9K5V04 = n9K5BasePoly 2 := by rfl
theorem n9K5Combo05 : n9K5V05 = n9K5BasePoly 0 + n9K5BasePoly 2 := by
  simp [n9K5V05, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo06 : n9K5V06 = n9K5BasePoly 1 + n9K5BasePoly 2 := by
  simp [n9K5V06, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo07 : n9K5V07 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 2 := by
  simp [n9K5V07, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo08 : n9K5V08 = n9K5BasePoly 3 := by rfl
theorem n9K5Combo09 : n9K5V09 = n9K5BasePoly 0 + n9K5BasePoly 3 := by
  simp [n9K5V09, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo10 : n9K5V10 = n9K5BasePoly 1 + n9K5BasePoly 3 := by
  simp [n9K5V10, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo11 : n9K5V11 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 3 := by
  simp [n9K5V11, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo12 : n9K5V12 = n9K5BasePoly 2 + n9K5BasePoly 3 := by
  simp [n9K5V12, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo13 : n9K5V13 = n9K5BasePoly 0 + n9K5BasePoly 2 + n9K5BasePoly 3 := by
  simp [n9K5V13, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo14 : n9K5V14 = n9K5BasePoly 1 + n9K5BasePoly 2 + n9K5BasePoly 3 := by
  simp [n9K5V14, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo15 : n9K5V15 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 2 + n9K5BasePoly 3 := by
  simp [n9K5V15, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo16 : n9K5V16 = n9K5BasePoly 4 := by rfl
theorem n9K5Combo17 : n9K5V17 = n9K5BasePoly 0 + n9K5BasePoly 4 := by
  simp [n9K5V17, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo18 : n9K5V18 = n9K5BasePoly 1 + n9K5BasePoly 4 := by
  simp [n9K5V18, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo19 : n9K5V19 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 4 := by
  simp [n9K5V19, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo20 : n9K5V20 = n9K5BasePoly 2 + n9K5BasePoly 4 := by
  simp [n9K5V20, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo21 : n9K5V21 = n9K5BasePoly 0 + n9K5BasePoly 2 + n9K5BasePoly 4 := by
  simp [n9K5V21, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo22 : n9K5V22 = n9K5BasePoly 1 + n9K5BasePoly 2 + n9K5BasePoly 4 := by
  simp [n9K5V22, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo23 : n9K5V23 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 2 + n9K5BasePoly 4 := by
  simp [n9K5V23, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo24 : n9K5V24 = n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V24, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo25 : n9K5V25 = n9K5BasePoly 0 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V25, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo26 : n9K5V26 = n9K5BasePoly 1 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V26, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo27 : n9K5V27 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V27, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo28 : n9K5V28 = n9K5BasePoly 2 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V28, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo29 : n9K5V29 = n9K5BasePoly 0 + n9K5BasePoly 2 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V29, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo30 : n9K5V30 = n9K5BasePoly 1 + n9K5BasePoly 2 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V30, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n9K5Combo31 : n9K5V31 = n9K5BasePoly 0 + n9K5BasePoly 1 + n9K5BasePoly 2 + n9K5BasePoly 3 + n9K5BasePoly 4 := by
  simp [n9K5V31, n9K5BasePoly, n9K5V01, n9K5V02, n9K5V04, n9K5V08, n9K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
#print axioms n9K5Combo03
#print axioms n9K5Combo31
