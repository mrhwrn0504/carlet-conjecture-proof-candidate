import Carlet.N11FieldBridgeProbe
import Carlet.Frobenius17Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def e11V01 : P17 := 1
def e11I01 : P17 := 1
def e11Q01 : P17 := 0
lemma e11Inv01 : e11V01*e11I01 + 1 = f*e11Q01 := by
  unfold e11V01 e11I01 e11Q01 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V02 : P17 := X^1 + X^3
def e11I02 : P17 := 1 + X^3 + X^5 + X^7 + X^9 + X^10
def e11Q02 : P17 := 1 + X^1 + X^2
lemma e11Inv02 : e11V02*e11I02 + 1 = f*e11Q02 := by
  unfold e11V02 e11I02 e11Q02 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V03 : P17 := 1 + X^1 + X^3
def e11I03 : P17 := 1 + X^2 + X^3 + X^5 + X^8 + X^9 + X^10
def e11Q03 : P17 := X^1 + X^2
lemma e11Inv03 : e11V03*e11I03 + 1 = f*e11Q03 := by
  unfold e11V03 e11I03 e11Q03 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V04 : P17 := X^4 + X^6
def e11I04 : P17 := 1 + X^1 + X^2 + X^4 + X^6 + X^7 + X^8 + X^10
def e11Q04 : P17 := 1 + X^2 + X^5
lemma e11Inv04 : e11V04*e11I04 + 1 = f*e11Q04 := by
  unfold e11V04 e11I04 e11Q04 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V05 : P17 := 1 + X^4 + X^6
def e11I05 : P17 := X^1 + X^5 + X^6 + X^9 + X^10
def e11Q05 : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^5
lemma e11Inv05 : e11V05*e11I05 + 1 = f*e11Q05 := by
  unfold e11V05 e11I05 e11Q05 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V06 : P17 := X^1 + X^3 + X^4 + X^6
def e11I06 : P17 := X^3 + X^4 + X^5 + X^6 + X^8 + X^10
def e11Q06 : P17 := 1 + X^2 + X^5
lemma e11Inv06 : e11V06*e11I06 + 1 = f*e11Q06 := by
  unfold e11V06 e11I06 e11Q06 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V07 : P17 := 1 + X^1 + X^3 + X^4 + X^6
def e11I07 : P17 := 1 + X^2 + X^5 + X^6 + X^10
def e11Q07 : P17 := X^1 + X^2 + X^3 + X^5
lemma e11Inv07 : e11V07*e11I07 + 1 = f*e11Q07 := by
  unfold e11V07 e11I07 e11Q07 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V08 : P17 := X^1 + X^8
def e11I08 : P17 := X^1 + X^2 + X^3 + X^6 + X^7 + X^8 + X^9
def e11Q08 : P17 := 1 + X^3 + X^4 + X^5 + X^6
lemma e11Inv08 : e11V08*e11I08 + 1 = f*e11Q08 := by
  unfold e11V08 e11I08 e11Q08 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V09 : P17 := 1 + X^1 + X^8
def e11I09 : P17 := 1 + X^4 + X^6 + X^7
def e11Q09 : P17 := X^1 + X^3 + X^4
lemma e11Inv09 : e11V09*e11I09 + 1 = f*e11Q09 := by
  unfold e11V09 e11I09 e11Q09 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V10 : P17 := X^3 + X^8
def e11I10 : P17 := X^2 + X^4 + X^5 + X^7 + X^8 + X^9
def e11Q10 : P17 := 1 + X^2 + X^4 + X^5 + X^6
lemma e11Inv10 : e11V10*e11I10 + 1 = f*e11Q10 := by
  unfold e11V10 e11I10 e11Q10 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V11 : P17 := 1 + X^3 + X^8
def e11I11 : P17 := 1 + X^1 + X^3 + X^4 + X^6 + X^8
def e11Q11 : P17 := X^1 + X^3 + X^5
lemma e11Inv11 : e11V11*e11I11 + 1 = f*e11Q11 := by
  unfold e11V11 e11I11 e11Q11 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V12 : P17 := X^1 + X^4 + X^6 + X^8
def e11I12 : P17 := 1 + X^1 + X^5 + X^6 + X^9
def e11Q12 : P17 := 1 + X^1 + X^3 + X^4 + X^6
lemma e11Inv12 : e11V12*e11I12 + 1 = f*e11Q12 := by
  unfold e11V12 e11I12 e11Q12 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V13 : P17 := 1 + X^1 + X^4 + X^6 + X^8
def e11I13 : P17 := 1 + X^1 + X^2 + X^4 + X^8
def e11Q13 : P17 := X^3 + X^5
lemma e11Inv13 : e11V13*e11I13 + 1 = f*e11Q13 := by
  unfold e11V13 e11I13 e11Q13 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V14 : P17 := X^3 + X^4 + X^6 + X^8
def e11I14 : P17 := 1 + X^1 + X^5 + X^6 + X^7 + X^8 + X^10
def e11Q14 : P17 := 1 + X^2 + X^3 + X^4 + X^7
lemma e11Inv14 : e11V14*e11I14 + 1 = f*e11Q14 := by
  unfold e11V14 e11I14 e11Q14 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e11V15 : P17 := 1 + X^3 + X^4 + X^6 + X^8
def e11I15 : P17 := X^1 + X^3 + X^6 + X^10
def e11Q15 : P17 := 1 + X^1 + X^2 + X^5 + X^7
lemma e11Inv15 : e11V15*e11I15 + 1 = f*e11Q15 := by
  unfold e11V15 e11I15 e11Q15 f
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma e11InverseSum : e11I01 + e11I02 + e11I03 + e11I04 + e11I05 + e11I06 + e11I07 + e11I08 + e11I09 + e11I10 + e11I11 + e11I12 + e11I13 + e11I14 + e11I15 = 0 := by
  unfold e11I01 e11I02 e11I03 e11I04 e11I05 e11I06 e11I07 e11I08 e11I09 e11I10 e11I11 e11I12 e11I13 e11I14 e11I15
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms e11Inv01
#print axioms e11Inv15
#print axioms e11InverseSum
