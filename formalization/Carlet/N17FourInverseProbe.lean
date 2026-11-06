import Carlet.N17FieldBridgeProbe
import Carlet.Frobenius17Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def e17V01 : P17 := 1
def e17I01 : P17 := 1
def e17Q01 : P17 := 0
lemma e17Inv01 : e17V01 * e17I01 + 1 = f17 * e17Q01 := by
  unfold e17V01 e17I01 e17Q01 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V02 : P17 := X^4 + X^5 + X^7 + X^12 + X^13 + X^14 + X^15 + X^16
def e17I02 : P17 := 1 + X^1 + X^6 + X^7 + X^8 + X^11 + X^14 + X^15 + X^16
def e17Q02 : P17 := 1 + X^3 + X^4 + X^8 + X^10 + X^11 + X^12 + X^13 + X^15
lemma e17Inv02 : e17V02 * e17I02 + 1 = f17 * e17Q02 := by
  unfold e17V02 e17I02 e17Q02 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V03 : P17 := 1 + X^4 + X^5 + X^7 + X^12 + X^13 + X^14 + X^15 + X^16
def e17I03 : P17 := 1 + X^1 + X^4 + X^6 + X^7 + X^8 + X^13 + X^15
def e17Q03 : P17 := X^1 + X^4 + X^7 + X^8 + X^9 + X^13 + X^14
lemma e17Inv03 : e17V03 * e17I03 + 1 = f17 * e17Q03 := by
  unfold e17V03 e17I03 e17Q03 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V04 : P17 := 1 + X^1 + X^2 + X^7 + X^8 + X^9 + X^10 + X^11 + X^12 + X^14
def e17I04 : P17 := 1 + X^4 + X^5 + X^6 + X^7 + X^9 + X^15 + X^16
def e17Q04 : P17 := X^1 + X^2 + X^5 + X^6 + X^11 + X^12 + X^13
lemma e17Inv04 : e17V04 * e17I04 + 1 = f17 * e17Q04 := by
  unfold e17V04 e17I04 e17Q04 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V05 : P17 := X^1 + X^2 + X^7 + X^8 + X^9 + X^10 + X^11 + X^12 + X^14
def e17I05 : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^10 + X^13 + X^14 + X^15
def e17Q05 : P17 := 1 + X^1 + X^3 + X^4 + X^6 + X^8 + X^11 + X^12
lemma e17Inv05 : e17V05 * e17I05 + 1 = f17 * e17Q05 := by
  unfold e17V05 e17I05 e17Q05 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V06 : P17 := 1 + X^1 + X^2 + X^4 + X^5 + X^8 + X^9 + X^10 + X^11 + X^13 + X^15 + X^16
def e17I06 : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^10 + X^11 + X^12 + X^13 + X^14 + X^16
def e17Q06 : P17 := X^2 + X^3 + X^7 + X^12 + X^13 + X^14 + X^15
lemma e17Inv06 : e17V06 * e17I06 + 1 = f17 * e17Q06 := by
  unfold e17V06 e17I06 e17Q06 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V07 : P17 := X^1 + X^2 + X^4 + X^5 + X^8 + X^9 + X^10 + X^11 + X^13 + X^15 + X^16
def e17I07 : P17 := X^3 + X^4 + X^5 + X^6 + X^7 + X^10 + X^11 + X^12 + X^13 + X^14 + X^16
def e17Q07 : P17 := 1 + X^3 + X^4 + X^6 + X^12 + X^13 + X^14 + X^15
lemma e17Inv07 : e17V07 * e17I07 + 1 = f17 * e17Q07 := by
  unfold e17V07 e17I07 e17Q07 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V08 : P17 := X^1 + X^3 + X^9 + X^11 + X^13 + X^14 + X^16
def e17I08 : P17 := 1 + X^1 + X^5 + X^6 + X^7 + X^8 + X^9 + X^11 + X^12 + X^13
def e17Q08 : P17 := 1 + X^1 + X^2 + X^5 + X^6 + X^7 + X^8 + X^11 + X^12
lemma e17Inv08 : e17V08 * e17I08 + 1 = f17 * e17Q08 := by
  unfold e17V08 e17I08 e17Q08 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V09 : P17 := 1 + X^1 + X^3 + X^9 + X^11 + X^13 + X^14 + X^16
def e17I09 : P17 := 1 + X^5 + X^6 + X^9 + X^10 + X^11 + X^12 + X^16
def e17Q09 : P17 := X^1 + X^3 + X^4 + X^5 + X^6 + X^11 + X^12 + X^13 + X^15
lemma e17Inv09 : e17V09 * e17I09 + 1 = f17 * e17Q09 := by
  unfold e17V09 e17I09 e17Q09 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V10 : P17 := X^1 + X^3 + X^4 + X^5 + X^7 + X^9 + X^11 + X^12 + X^15
def e17I10 : P17 := X^1 + X^3 + X^6 + X^7 + X^9 + X^10 + X^12
def e17Q10 : P17 := 1 + X^2 + X^3 + X^6 + X^8 + X^10
lemma e17Inv10 : e17V10 * e17I10 + 1 = f17 * e17Q10 := by
  unfold e17V10 e17I10 e17Q10 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V11 : P17 := 1 + X^1 + X^3 + X^4 + X^5 + X^7 + X^9 + X^11 + X^12 + X^15
def e17I11 : P17 := 1 + X^3 + X^4 + X^5 + X^6 + X^7 + X^10 + X^11 + X^12 + X^13 + X^14 + X^15
def e17Q11 : P17 := X^1 + X^5 + X^6 + X^7 + X^8 + X^9 + X^11 + X^12 + X^13
lemma e17Inv11 : e17V11 * e17I11 + 1 = f17 * e17Q11 := by
  unfold e17V11 e17I11 e17Q11 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V12 : P17 := 1 + X^2 + X^3 + X^7 + X^8 + X^10 + X^12 + X^13 + X^16
def e17I12 : P17 := X^1 + X^2 + X^3 + X^5 + X^6 + X^7 + X^8 + X^13 + X^15
def e17Q12 : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^6 + X^7 + X^9 + X^10 + X^11 + X^12 + X^14
lemma e17Inv12 : e17V12 * e17I12 + 1 = f17 * e17Q12 := by
  unfold e17V12 e17I12 e17Q12 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V13 : P17 := X^2 + X^3 + X^7 + X^8 + X^10 + X^12 + X^13 + X^16
def e17I13 : P17 := X^1 + X^2 + X^6 + X^7 + X^8 + X^9 + X^11 + X^12 + X^13 + X^16
def e17Q13 : P17 := 1 + X^5 + X^8 + X^10 + X^15
lemma e17Inv13 : e17V13 * e17I13 + 1 = f17 * e17Q13 := by
  unfold e17V13 e17I13 e17Q13 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V14 : P17 := 1 + X^2 + X^3 + X^4 + X^5 + X^8 + X^10 + X^14 + X^15
def e17I14 : P17 := 1 + X^1 + X^3 + X^4 + X^7 + X^9 + X^11 + X^13 + X^14 + X^16
def e17Q14 : P17 := X^1 + X^2 + X^3 + X^7 + X^8 + X^10 + X^12 + X^13 + X^14
lemma e17Inv14 : e17V14 * e17I14 + 1 = f17 * e17Q14 := by
  unfold e17V14 e17I14 e17Q14 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def e17V15 : P17 := X^2 + X^3 + X^4 + X^5 + X^8 + X^10 + X^14 + X^15
def e17I15 : P17 := X^1 + X^3 + X^4 + X^7 + X^12 + X^13 + X^16
def e17Q15 : P17 := 1 + X^4 + X^6 + X^7 + X^11 + X^13 + X^14
lemma e17Inv15 : e17V15 * e17I15 + 1 = f17 * e17Q15 := by
  unfold e17V15 e17I15 e17Q15 f17
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma e17InverseSum : e17I01 + e17I02 + e17I03 + e17I04 + e17I05 + e17I06 + e17I07 + e17I08 + e17I09 + e17I10 + e17I11 + e17I12 + e17I13 + e17I14 + e17I15 = 0 := by
  unfold e17I01 e17I02 e17I03 e17I04 e17I05 e17I06 e17I07 e17I08 e17I09 e17I10 e17I11 e17I12 e17I13 e17I14 e17I15
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms e17Inv01
#print axioms e17Inv15
#print axioms e17InverseSum
