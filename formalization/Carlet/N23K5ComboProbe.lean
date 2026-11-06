import Carlet.N23K5InverseProbe
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def n23K5BasePoly : Fin 5 → P17
| 0 => n23K5V01
| 1 => n23K5V02
| 2 => n23K5V04
| 3 => n23K5V08
| 4 => n23K5V16
theorem n23K5Combo01 : n23K5V01 = n23K5BasePoly 0 := by rfl
theorem n23K5Combo02 : n23K5V02 = n23K5BasePoly 1 := by rfl
theorem n23K5Combo03 : n23K5V03 = n23K5BasePoly 0 + n23K5BasePoly 1 := by
  simp [n23K5V03, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo04 : n23K5V04 = n23K5BasePoly 2 := by rfl
theorem n23K5Combo05 : n23K5V05 = n23K5BasePoly 0 + n23K5BasePoly 2 := by
  simp [n23K5V05, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo06 : n23K5V06 = n23K5BasePoly 1 + n23K5BasePoly 2 := by
  simp [n23K5V06, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo07 : n23K5V07 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 2 := by
  simp [n23K5V07, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo08 : n23K5V08 = n23K5BasePoly 3 := by rfl
theorem n23K5Combo09 : n23K5V09 = n23K5BasePoly 0 + n23K5BasePoly 3 := by
  simp [n23K5V09, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo10 : n23K5V10 = n23K5BasePoly 1 + n23K5BasePoly 3 := by
  simp [n23K5V10, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo11 : n23K5V11 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 3 := by
  simp [n23K5V11, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo12 : n23K5V12 = n23K5BasePoly 2 + n23K5BasePoly 3 := by
  simp [n23K5V12, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo13 : n23K5V13 = n23K5BasePoly 0 + n23K5BasePoly 2 + n23K5BasePoly 3 := by
  simp [n23K5V13, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo14 : n23K5V14 = n23K5BasePoly 1 + n23K5BasePoly 2 + n23K5BasePoly 3 := by
  simp [n23K5V14, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo15 : n23K5V15 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 2 + n23K5BasePoly 3 := by
  simp [n23K5V15, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo16 : n23K5V16 = n23K5BasePoly 4 := by rfl
theorem n23K5Combo17 : n23K5V17 = n23K5BasePoly 0 + n23K5BasePoly 4 := by
  simp [n23K5V17, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo18 : n23K5V18 = n23K5BasePoly 1 + n23K5BasePoly 4 := by
  simp [n23K5V18, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo19 : n23K5V19 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 4 := by
  simp [n23K5V19, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo20 : n23K5V20 = n23K5BasePoly 2 + n23K5BasePoly 4 := by
  simp [n23K5V20, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo21 : n23K5V21 = n23K5BasePoly 0 + n23K5BasePoly 2 + n23K5BasePoly 4 := by
  simp [n23K5V21, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo22 : n23K5V22 = n23K5BasePoly 1 + n23K5BasePoly 2 + n23K5BasePoly 4 := by
  simp [n23K5V22, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo23 : n23K5V23 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 2 + n23K5BasePoly 4 := by
  simp [n23K5V23, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo24 : n23K5V24 = n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V24, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo25 : n23K5V25 = n23K5BasePoly 0 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V25, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo26 : n23K5V26 = n23K5BasePoly 1 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V26, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo27 : n23K5V27 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V27, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo28 : n23K5V28 = n23K5BasePoly 2 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V28, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo29 : n23K5V29 = n23K5BasePoly 0 + n23K5BasePoly 2 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V29, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo30 : n23K5V30 = n23K5BasePoly 1 + n23K5BasePoly 2 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V30, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n23K5Combo31 : n23K5V31 = n23K5BasePoly 0 + n23K5BasePoly 1 + n23K5BasePoly 2 + n23K5BasePoly 3 + n23K5BasePoly 4 := by
  simp [n23K5V31, n23K5BasePoly, n23K5V01, n23K5V02, n23K5V04, n23K5V08, n23K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
#print axioms n23K5Combo03
#print axioms n23K5Combo31
