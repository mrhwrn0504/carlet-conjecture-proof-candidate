import Carlet.Frobenius9Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
def n9K5V01 : P17 := X^2 + X^3 + X^4 + X^5 + X^6 + X^8
def n9K5I01 : P17 := X^1 + X^3 + X^4 + X^5 + X^6
def n9K5Q01 : P17 := 1 + X^1 + X^2 + X^4 + X^5
lemma n9K5Inv01 : n9K5V01*n9K5I01 + 1 = f9*n9K5Q01 := by
  unfold n9K5V01 n9K5I01 n9K5Q01 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V02 : P17 := X^2 + X^6 + X^8
def n9K5I02 : P17 := 1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^8
def n9K5Q02 : P17 := 1 + X^1 + X^4 + X^7
lemma n9K5Inv02 : n9K5V02*n9K5I02 + 1 = f9*n9K5Q02 := by
  unfold n9K5V02 n9K5I02 n9K5Q02 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V03 : P17 := X^3 + X^4 + X^5
def n9K5I03 : P17 := X^2 + X^3 + X^5 + X^8
def n9K5Q03 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma n9K5Inv03 : n9K5V03*n9K5I03 + 1 = f9*n9K5Q03 := by
  unfold n9K5V03 n9K5I03 n9K5Q03 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V04 : P17 := X^2 + X^3 + X^5 + X^6
def n9K5I04 : P17 := X^3 + X^4 + X^5 + X^7
def n9K5Q04 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma n9K5Inv04 : n9K5V04*n9K5I04 + 1 = f9*n9K5Q04 := by
  unfold n9K5V04 n9K5I04 n9K5Q04 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V05 : P17 := X^4 + X^8
def n9K5I05 : P17 := 1 + X^1 + X^6 + X^7 + X^8
def n9K5Q05 : P17 := 1 + X^1 + X^2 + X^3 + X^5 + X^6 + X^7
lemma n9K5Inv05 : n9K5V05*n9K5I05 + 1 = f9*n9K5Q05 := by
  unfold n9K5V05 n9K5I05 n9K5Q05 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V06 : P17 := X^3 + X^5 + X^8
def n9K5I06 : P17 := X^1 + X^2 + X^4 + X^6
def n9K5Q06 : P17 := 1 + X^1 + X^2 + X^3 + X^5
lemma n9K5Inv06 : n9K5V06*n9K5I06 + 1 = f9*n9K5Q06 := by
  unfold n9K5V06 n9K5I06 n9K5Q06 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V07 : P17 := X^2 + X^4 + X^6
def n9K5I07 : P17 := X^1 + X^4 + X^5 + X^6 + X^8
def n9K5Q07 : P17 := 1 + X^1 + X^2 + X^5
lemma n9K5Inv07 : n9K5V07*n9K5I07 + 1 = f9*n9K5Q07 := by
  unfold n9K5V07 n9K5I07 n9K5Q07 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V08 : P17 := X^1 + X^2 + X^5 + X^7
def n9K5I08 : P17 := X^2 + X^4 + X^8
def n9K5Q08 : P17 := 1 + X^1 + X^2 + X^4 + X^6
lemma n9K5Inv08 : n9K5V08*n9K5I08 + 1 = f9*n9K5Q08 := by
  unfold n9K5V08 n9K5I08 n9K5Q08 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V09 : P17 := X^1 + X^3 + X^4 + X^6 + X^7 + X^8
def n9K5I09 : P17 := 1 + X^1 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8
def n9K5Q09 : P17 := 1 + X^2 + X^4 + X^5 + X^7
lemma n9K5Inv09 : n9K5V09*n9K5I09 + 1 = f9*n9K5Q09 := by
  unfold n9K5V09 n9K5I09 n9K5Q09 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V10 : P17 := X^1 + X^5 + X^6 + X^7 + X^8
def n9K5I10 : P17 := 1 + X^2 + X^4 + X^6 + X^7 + X^8
def n9K5Q10 : P17 := 1 + X^3 + X^4 + X^5 + X^7
lemma n9K5Inv10 : n9K5V10*n9K5I10 + 1 = f9*n9K5Q10 := by
  unfold n9K5V10 n9K5I10 n9K5Q10 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V11 : P17 := X^1 + X^2 + X^3 + X^4 + X^7
def n9K5I11 : P17 := X^1 + X^4 + X^8
def n9K5Q11 : P17 := 1 + X^1 + X^3 + X^6
lemma n9K5Inv11 : n9K5V11*n9K5I11 + 1 = f9*n9K5Q11 := by
  unfold n9K5V11 n9K5I11 n9K5Q11 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V12 : P17 := X^1 + X^3 + X^6 + X^7
def n9K5I12 : P17 := X^4 + X^6
def n9K5Q12 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma n9K5Inv12 : n9K5V12*n9K5I12 + 1 = f9*n9K5Q12 := by
  unfold n9K5V12 n9K5I12 n9K5Q12 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V13 : P17 := X^1 + X^2 + X^4 + X^5 + X^7 + X^8
def n9K5I13 : P17 := 1 + X^7
def n9K5Q13 : P17 := 1 + X^2 + X^3 + X^5 + X^6
lemma n9K5Inv13 : n9K5V13*n9K5I13 + 1 = f9*n9K5Q13 := by
  unfold n9K5V13 n9K5I13 n9K5Q13 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V14 : P17 := X^1 + X^2 + X^3 + X^7 + X^8
def n9K5I14 : P17 := 1 + X^1 + X^2 + X^3 + X^5 + X^6 + X^7 + X^8
def n9K5Q14 : P17 := 1 + X^3 + X^7
lemma n9K5Inv14 : n9K5V14*n9K5I14 + 1 = f9*n9K5Q14 := by
  unfold n9K5V14 n9K5I14 n9K5Q14 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V15 : P17 := X^1 + X^4 + X^5 + X^6 + X^7
def n9K5I15 : P17 := 1 + X^5 + X^6
def n9K5Q15 : P17 := 1 + X^4
lemma n9K5Inv15 : n9K5V15*n9K5I15 + 1 = f9*n9K5Q15 := by
  unfold n9K5V15 n9K5I15 n9K5Q15 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V16 : P17 := X^1 + X^2 + X^3 + X^4 + X^5 + X^7
def n9K5I16 : P17 := X^2 + X^4 + X^5 + X^6 + X^7
def n9K5Q16 : P17 := 1 + X^1 + X^2 + X^4 + X^5
lemma n9K5Inv16 : n9K5V16*n9K5I16 + 1 = f9*n9K5Q16 := by
  unfold n9K5V16 n9K5I16 n9K5Q16 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V17 : P17 := X^1 + X^6 + X^7 + X^8
def n9K5I17 : P17 := 1 + X^2 + X^3 + X^5 + X^7 + X^8
def n9K5Q17 : P17 := 1 + X^3 + X^7
lemma n9K5Inv17 : n9K5V17*n9K5I17 + 1 = f9*n9K5Q17 := by
  unfold n9K5V17 n9K5I17 n9K5Q17 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V18 : P17 := X^1 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8
def n9K5I18 : P17 := 1 + X^3 + X^5 + X^6 + X^7
def n9K5Q18 : P17 := 1 + X^3 + X^4 + X^6
lemma n9K5Inv18 : n9K5V18*n9K5I18 + 1 = f9*n9K5Q18 := by
  unfold n9K5V18 n9K5I18 n9K5Q18 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V19 : P17 := X^1 + X^2 + X^7
def n9K5I19 : P17 := 1 + X^1 + X^2 + X^3 + X^7 + X^8
def n9K5Q19 : P17 := 1 + X^5 + X^6
lemma n9K5Inv19 : n9K5V19*n9K5I19 + 1 = f9*n9K5Q19 := by
  unfold n9K5V19 n9K5I19 n9K5Q19 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V20 : P17 := X^1 + X^4 + X^6 + X^7
def n9K5I20 : P17 := X^1 + X^5 + X^6 + X^7
def n9K5Q20 : P17 := 1 + X^1 + X^5
lemma n9K5Inv20 : n9K5V20*n9K5I20 + 1 = f9*n9K5Q20 := by
  unfold n9K5V20 n9K5I20 n9K5Q20 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V21 : P17 := X^1 + X^2 + X^3 + X^5 + X^7 + X^8
def n9K5I21 : P17 := X^3 + X^4 + X^5 + X^6 + X^7
def n9K5Q21 : P17 := 1 + X^1 + X^2 + X^3 + X^6
lemma n9K5Inv21 : n9K5V21*n9K5I21 + 1 = f9*n9K5Q21 := by
  unfold n9K5V21 n9K5I21 n9K5Q21 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V22 : P17 := X^1 + X^2 + X^4 + X^7 + X^8
def n9K5I22 : P17 := X^3 + X^4 + X^5 + X^6 + X^7 + X^8
def n9K5Q22 : P17 := 1 + X^1 + X^2 + X^3 + X^7
lemma n9K5Inv22 : n9K5V22*n9K5I22 + 1 = f9*n9K5Q22 := by
  unfold n9K5V22 n9K5I22 n9K5Q22 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V23 : P17 := X^1 + X^3 + X^5 + X^6 + X^7
def n9K5I23 : P17 := 1 + X^2 + X^4 + X^6 + X^7
def n9K5Q23 : P17 := 1 + X^5
lemma n9K5Inv23 : n9K5V23*n9K5I23 + 1 = f9*n9K5Q23 := by
  unfold n9K5V23 n9K5I23 n9K5Q23 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V24 : P17 := X^3 + X^4
def n9K5I24 : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^5 + X^7
def n9K5Q24 : P17 := 1 + X^1 + X^2
lemma n9K5Inv24 : n9K5V24*n9K5I24 + 1 = f9*n9K5Q24 := by
  unfold n9K5V24 n9K5I24 n9K5Q24 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V25 : P17 := X^2 + X^5 + X^6 + X^8
def n9K5I25 : P17 := 1 + X^2 + X^5 + X^6 + X^7 + X^8
def n9K5Q25 : P17 := 1 + X^1 + X^4 + X^6 + X^7
lemma n9K5Inv25 : n9K5V25*n9K5I25 + 1 = f9*n9K5Q25 := by
  unfold n9K5V25 n9K5I25 n9K5Q25 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V26 : P17 := X^2 + X^3 + X^4 + X^6 + X^8
def n9K5I26 : P17 := X^3 + X^4 + X^5 + X^6 + X^8
def n9K5Q26 : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^7
lemma n9K5Inv26 : n9K5V26*n9K5I26 + 1 = f9*n9K5Q26 := by
  unfold n9K5V26 n9K5I26 n9K5Q26 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V27 : P17 := X^5
def n9K5I27 : P17 := 1 + X^4 + X^5 + X^6 + X^7 + X^8
def n9K5Q27 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma n9K5Inv27 : n9K5V27*n9K5I27 + 1 = f9*n9K5Q27 := by
  unfold n9K5V27 n9K5I27 n9K5Q27 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V28 : P17 := X^2 + X^4 + X^5 + X^6
def n9K5I28 : P17 := 1 + X^2 + X^4 + X^5 + X^7 + X^8
def n9K5Q28 : P17 := 1 + X^1 + X^5
lemma n9K5Inv28 : n9K5V28*n9K5I28 + 1 = f9*n9K5Q28 := by
  unfold n9K5V28 n9K5I28 n9K5Q28 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V29 : P17 := X^3 + X^8
def n9K5I29 : P17 := X^1 + X^3 + X^4 + X^7
def n9K5Q29 : P17 := 1 + X^1 + X^2 + X^3 + X^6
lemma n9K5Inv29 : n9K5V29*n9K5I29 + 1 = f9*n9K5Q29 := by
  unfold n9K5V29 n9K5I29 n9K5Q29 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V30 : P17 := X^4 + X^5 + X^8
def n9K5I30 : P17 := 1 + X^2 + X^5 + X^6 + X^8
def n9K5Q30 : P17 := 1 + X^1 + X^2 + X^3 + X^5 + X^7
lemma n9K5Inv30 : n9K5V30*n9K5I30 + 1 = f9*n9K5Q30 := by
  unfold n9K5V30 n9K5I30 n9K5Q30 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n9K5V31 : P17 := X^2 + X^3 + X^6
def n9K5I31 : P17 := X^1 + X^4 + X^7 + X^8
def n9K5Q31 : P17 := 1 + X^1 + X^2 + X^4 + X^5
lemma n9K5Inv31 : n9K5V31*n9K5I31 + 1 = f9*n9K5Q31 := by
  unfold n9K5V31 n9K5I31 n9K5Q31 f9
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma n9K5InverseSum : n9K5I01 + n9K5I02 + n9K5I03 + n9K5I04 + n9K5I05 + n9K5I06 + n9K5I07 + n9K5I08 + n9K5I09 + n9K5I10 + n9K5I11 + n9K5I12 + n9K5I13 + n9K5I14 + n9K5I15 + n9K5I16 + n9K5I17 + n9K5I18 + n9K5I19 + n9K5I20 + n9K5I21 + n9K5I22 + n9K5I23 + n9K5I24 + n9K5I25 + n9K5I26 + n9K5I27 + n9K5I28 + n9K5I29 + n9K5I30 + n9K5I31 = 0 := by
  unfold n9K5I01 n9K5I02 n9K5I03 n9K5I04 n9K5I05 n9K5I06 n9K5I07 n9K5I08 n9K5I09 n9K5I10 n9K5I11 n9K5I12 n9K5I13 n9K5I14 n9K5I15 n9K5I16 n9K5I17 n9K5I18 n9K5I19 n9K5I20 n9K5I21 n9K5I22 n9K5I23 n9K5I24 n9K5I25 n9K5I26 n9K5I27 n9K5I28 n9K5I29 n9K5I30 n9K5I31
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms n9K5Inv01
#print axioms n9K5Inv31
#print axioms n9K5InverseSum
