import Carlet.Frobenius9Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def d9V01 : P17 := 1
def d9I01 : P17 := 1
def d9Q01 : P17 := 0
lemma d9Inv01 : d9V01*d9I01 + 1 = f9*d9Q01 := by
  unfold d9V01 d9I01 d9Q01 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V02 : P17 := X^3 + X^5
def d9I02 : P17 := X^2 + X^4 + X^7 + X^8
def d9Q02 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma d9Inv02 : d9V02*d9I02 + 1 = f9*d9Q02 := by
  unfold d9V02 d9I02 d9Q02 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V03 : P17 := 1 + X^3 + X^5
def d9I03 : P17 := X^2 + X^3 + X^6 + X^7 + X^8
def d9Q03 : P17 := 1 + X^1 + X^3 + X^4
lemma d9Inv03 : d9V03*d9I03 + 1 = f9*d9Q03 := by
  unfold d9V03 d9I03 d9Q03 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V04 : P17 := X^4 + X^6
def d9I04 : P17 := X^1 + X^3 + X^6 + X^7
def d9Q04 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma d9Inv04 : d9V04*d9I04 + 1 = f9*d9Q04 := by
  unfold d9V04 d9I04 d9Q04 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V05 : P17 := 1 + X^4 + X^6
def d9I05 : P17 := X^1 + X^4 + X^5 + X^6 + X^7 + X^8
def d9Q05 : P17 := 1 + X^4 + X^5
lemma d9Inv05 : d9V05*d9I05 + 1 = f9*d9Q05 := by
  unfold d9V05 d9I05 d9Q05 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V06 : P17 := X^3 + X^4 + X^5 + X^6
def d9I06 : P17 := X^2 + X^3 + X^7
def d9Q06 : P17 := 1 + X^1 + X^2 + X^3 + X^4
lemma d9Inv06 : d9V06*d9I06 + 1 = f9*d9Q06 := by
  unfold d9V06 d9I06 d9Q06 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V07 : P17 := 1 + X^3 + X^4 + X^5 + X^6
def d9I07 : P17 := X^1 + X^6 + X^7
def d9Q07 : P17 := 1 + X^4
lemma d9Inv07 : d9V07*d9I07 + 1 = f9*d9Q07 := by
  unfold d9V07 d9I07 d9Q07 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V08 : P17 := X^2 + X^7
def d9I08 : P17 := X^2 + X^4 + X^5 + X^8
def d9Q08 : P17 := 1 + X^1 + X^2 + X^3 + X^6
lemma d9Inv08 : d9V08*d9I08 + 1 = f9*d9Q08 := by
  unfold d9V08 d9I08 d9Q08 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V09 : P17 := 1 + X^2 + X^7
def d9I09 : P17 := X^1 + X^3 + X^7 + X^8
def d9Q09 : P17 := 1 + X^5 + X^6
lemma d9Inv09 : d9V09*d9I09 + 1 = f9*d9Q09 := by
  unfold d9V09 d9I09 d9Q09 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V10 : P17 := X^2 + X^3 + X^5 + X^7
def d9I10 : P17 := X^2 + X^4 + X^7
def d9Q10 : P17 := 1 + X^1 + X^2 + X^3 + X^5
lemma d9Inv10 : d9V10*d9I10 + 1 = f9*d9Q10 := by
  unfold d9V10 d9I10 d9Q10 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V11 : P17 := 1 + X^2 + X^3 + X^5 + X^7
def d9I11 : P17 := X^2 + X^3 + X^4 + X^7 + X^8
def d9Q11 : P17 := 1 + X^1 + X^3 + X^4 + X^5 + X^6
lemma d9Inv11 : d9V11*d9I11 + 1 = f9*d9Q11 := by
  unfold d9V11 d9I11 d9Q11 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V12 : P17 := X^2 + X^4 + X^6 + X^7
def d9I12 : P17 := X^1 + X^2 + X^3 + X^7
def d9Q12 : P17 := 1 + X^1 + X^2 + X^4 + X^5
lemma d9Inv12 : d9V12*d9I12 + 1 = f9*d9Q12 := by
  unfold d9V12 d9I12 d9Q12 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V13 : P17 := 1 + X^2 + X^4 + X^6 + X^7
def d9I13 : P17 := X^1 + X^3 + X^5 + X^6 + X^7
def d9Q13 : P17 := 1 + X^5
lemma d9Inv13 : d9V13*d9I13 + 1 = f9*d9Q13 := by
  unfold d9V13 d9I13 d9Q13 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V14 : P17 := X^2 + X^3 + X^4 + X^5 + X^6 + X^7
def d9I14 : P17 := 1 + X^1 + X^2 + X^3 + X^5 + X^8
def d9Q14 : P17 := 1 + X^1 + X^4 + X^5 + X^6
lemma d9Inv14 : d9V14*d9I14 + 1 = f9*d9Q14 := by
  unfold d9V14 d9I14 d9Q14 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def d9V15 : P17 := 1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7
def d9I15 : P17 := X^1 + X^4 + X^6 + X^7 + X^8
def d9Q15 : P17 := 1 + X^3 + X^4 + X^6
lemma d9Inv15 : d9V15*d9I15 + 1 = f9*d9Q15 := by
  unfold d9V15 d9I15 d9Q15 f9
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma d9InverseSum : d9I01 + d9I02 + d9I03 + d9I04 + d9I05 + d9I06 + d9I07 + d9I08 + d9I09 + d9I10 + d9I11 + d9I12 + d9I13 + d9I14 + d9I15 = 0 := by
  unfold d9I01 d9I02 d9I03 d9I04 d9I05 d9I06 d9I07 d9I08 d9I09 d9I10 d9I11 d9I12 d9I13 d9I14 d9I15
  ring_nf; simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms d9Inv01
#print axioms d9Inv15
#print axioms d9InverseSum
