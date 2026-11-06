import Carlet.N29K5InverseProbe
open Carlet
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
def n29K5BasePoly : Fin 5 → P17
| 0 => n29K5V01
| 1 => n29K5V02
| 2 => n29K5V04
| 3 => n29K5V08
| 4 => n29K5V16
theorem n29K5Combo01 : n29K5V01 = n29K5BasePoly 0 := by rfl
theorem n29K5Combo02 : n29K5V02 = n29K5BasePoly 1 := by rfl
theorem n29K5Combo03 : n29K5V03 = n29K5BasePoly 0 + n29K5BasePoly 1 := by
  simp [n29K5V03, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo04 : n29K5V04 = n29K5BasePoly 2 := by rfl
theorem n29K5Combo05 : n29K5V05 = n29K5BasePoly 0 + n29K5BasePoly 2 := by
  simp [n29K5V05, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo06 : n29K5V06 = n29K5BasePoly 1 + n29K5BasePoly 2 := by
  simp [n29K5V06, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo07 : n29K5V07 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 2 := by
  simp [n29K5V07, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo08 : n29K5V08 = n29K5BasePoly 3 := by rfl
theorem n29K5Combo09 : n29K5V09 = n29K5BasePoly 0 + n29K5BasePoly 3 := by
  simp [n29K5V09, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo10 : n29K5V10 = n29K5BasePoly 1 + n29K5BasePoly 3 := by
  simp [n29K5V10, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo11 : n29K5V11 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 3 := by
  simp [n29K5V11, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo12 : n29K5V12 = n29K5BasePoly 2 + n29K5BasePoly 3 := by
  simp [n29K5V12, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo13 : n29K5V13 = n29K5BasePoly 0 + n29K5BasePoly 2 + n29K5BasePoly 3 := by
  simp [n29K5V13, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo14 : n29K5V14 = n29K5BasePoly 1 + n29K5BasePoly 2 + n29K5BasePoly 3 := by
  simp [n29K5V14, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo15 : n29K5V15 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 2 + n29K5BasePoly 3 := by
  simp [n29K5V15, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo16 : n29K5V16 = n29K5BasePoly 4 := by rfl
theorem n29K5Combo17 : n29K5V17 = n29K5BasePoly 0 + n29K5BasePoly 4 := by
  simp [n29K5V17, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo18 : n29K5V18 = n29K5BasePoly 1 + n29K5BasePoly 4 := by
  simp [n29K5V18, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo19 : n29K5V19 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 4 := by
  simp [n29K5V19, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo20 : n29K5V20 = n29K5BasePoly 2 + n29K5BasePoly 4 := by
  simp [n29K5V20, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo21 : n29K5V21 = n29K5BasePoly 0 + n29K5BasePoly 2 + n29K5BasePoly 4 := by
  simp [n29K5V21, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo22 : n29K5V22 = n29K5BasePoly 1 + n29K5BasePoly 2 + n29K5BasePoly 4 := by
  simp [n29K5V22, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo23 : n29K5V23 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 2 + n29K5BasePoly 4 := by
  simp [n29K5V23, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo24 : n29K5V24 = n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V24, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo25 : n29K5V25 = n29K5BasePoly 0 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V25, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo26 : n29K5V26 = n29K5BasePoly 1 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V26, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo27 : n29K5V27 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V27, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo28 : n29K5V28 = n29K5BasePoly 2 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V28, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo29 : n29K5V29 = n29K5BasePoly 0 + n29K5BasePoly 2 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V29, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo30 : n29K5V30 = n29K5BasePoly 1 + n29K5BasePoly 2 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V30, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
theorem n29K5Combo31 : n29K5V31 = n29K5BasePoly 0 + n29K5BasePoly 1 + n29K5BasePoly 2 + n29K5BasePoly 3 + n29K5BasePoly 4 := by
  simp [n29K5V31, n29K5BasePoly, n29K5V01, n29K5V02, n29K5V04, n29K5V08, n29K5V16] <;> ring_nf <;> simp [c2_17,c3_17,c4_17,c5_17,c6_17,c7_17,c8_17,c9_17,c10_17,c11_17,c12_17,c13_17,c14_17,c15_17,c16_17,c17_17,c18_17,c19_17,c20_17,c21_17,c22_17,c23_17,c24_17]
#print axioms n29K5Combo03
#print axioms n29K5Combo31
