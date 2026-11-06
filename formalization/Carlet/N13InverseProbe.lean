import Carlet.Frobenius13Probe
import Mathlib.Tactic
import Mathlib.RingTheory.AdjoinRoot
open Polynomial
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
def cert13V01 : P13 := X^3 + X^4 + X^7 + X^8 + X^10 + X^12
def cert13I01 : P13 := X + X^7
def cert13Q01 : P13 := 1 + X + X^2 + X^4 + X^6
lemma cert13InvPoly01 : cert13V01 * cert13I01 + 1 = f13 * cert13Q01 := by
  unfold cert13V01 cert13I01 cert13Q01 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V02 : P13 := 1 + X + X^2 + X^3 + X^4 + X^6 + X^7 + X^9 + X^10 + X^11 + X^12
def cert13I02 : P13 := X + X^4 + X^7 + X^9 + X^11
def cert13Q02 : P13 := 1 + X^2 + X^3 + X^5 + X^9 + X^10
lemma cert13InvPoly02 : cert13V02 * cert13I02 + 1 = f13 * cert13Q02 := by
  unfold cert13V02 cert13I02 cert13Q02 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V03 : P13 := 1 + X + X^2 + X^6 + X^8 + X^9 + X^11
def cert13I03 : P13 := 1 + X^2 + X^5 + X^9 + X^10 + X^11 + X^12
def cert13Q03 : P13 := X + X^2 + X^5 + X^7 + X^9 + X^10
lemma cert13InvPoly03 : cert13V03 * cert13I03 + 1 = f13 * cert13Q03 := by
  unfold cert13V03 cert13I03 cert13Q03 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V04 : P13 := 1 + X + X^3 + X^4 + X^7 + X^9 + X^12
def cert13I04 : P13 := X^4 + X^9 + X^10 + X^11
def cert13Q04 : P13 := 1 + X + X^2 + X^4 + X^6 + X^7 + X^8 + X^9 + X^10
lemma cert13InvPoly04 : cert13V04 * cert13I04 + 1 = f13 * cert13Q04 := by
  unfold cert13V04 cert13I04 cert13Q04 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V05 : P13 := 1 + X + X^8 + X^9 + X^10
def cert13I05 : P13 := 1 + X + X^2 + X^3 + X^5 + X^6 + X^8 + X^10 + X^11
def cert13Q05 : P13 := X^4 + X^8
lemma cert13InvPoly05 : cert13V05 * cert13I05 + 1 = f13 * cert13Q05 := by
  unfold cert13V05 cert13I05 cert13Q05 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V06 : P13 := X^2 + X^6 + X^10 + X^11
def cert13I06 : P13 := 1 + X^2 + X^6 + X^8 + X^11
def cert13Q06 : P13 := 1 + X + X^3 + X^5 + X^6 + X^8 + X^9
lemma cert13InvPoly06 : cert13V06 * cert13I06 + 1 = f13 * cert13Q06 := by
  unfold cert13V06 cert13I06 cert13Q06 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V07 : P13 := X^2 + X^3 + X^4 + X^6 + X^7 + X^8 + X^11 + X^12
def cert13I07 : P13 := 1 + X + X^2 + X^4 + X^7 + X^8 + X^9 + X^10 + X^12
def cert13Q07 : P13 := 1 + X + X^3 + X^5 + X^6 + X^7 + X^9 + X^10 + X^11
lemma cert13InvPoly07 : cert13V07 * cert13I07 + 1 = f13 * cert13Q07 := by
  unfold cert13V07 cert13I07 cert13Q07 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V08 : P13 := X + X^2 + X^3 + X^5 + X^6 + X^8 + X^10
def cert13I08 : P13 := 1 + X^2 + X^3 + X^5 + X^6 + X^9 + X^10
def cert13Q08 : P13 := 1 + X^2 + X^4 + X^5 + X^6 + X^7
lemma cert13InvPoly08 : cert13V08 * cert13I08 + 1 = f13 * cert13Q08 := by
  unfold cert13V08 cert13I08 cert13Q08 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V09 : P13 := X + X^2 + X^4 + X^5 + X^6 + X^7 + X^12
def cert13I09 : P13 := 1 + X + X^3 + X^5 + X^6 + X^7 + X^8 + X^10 + X^11
def cert13Q09 : P13 := 1 + X^4 + X^6 + X^7 + X^9 + X^10
lemma cert13InvPoly09 : cert13V09 * cert13I09 + 1 = f13 * cert13Q09 := by
  unfold cert13V09 cert13I09 cert13Q09 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V10 : P13 := 1 + X^4 + X^5 + X^7 + X^8 + X^9 + X^11 + X^12
def cert13I10 : P13 := 1 + X^2 + X^3 + X^4 + X^5 + X^7 + X^8 + X^10 + X^11 + X^12
def cert13Q10 : P13 := X^2 + X^5 + X^6 + X^7 + X^11
lemma cert13InvPoly10 : cert13V10 * cert13I10 + 1 = f13 * cert13Q10 := by
  unfold cert13V10 cert13I10 cert13Q10 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V11 : P13 := 1 + X^3 + X^5 + X^9 + X^10 + X^11
def cert13I11 : P13 := X^3 + X^6 + X^7 + X^10 + X^11 + X^12
def cert13Q11 : P13 := 1 + X + X^2 + X^3 + X^4 + X^5 + X^6 + X^8 + X^10
lemma cert13InvPoly11 : cert13V11 * cert13I11 + 1 = f13 * cert13Q11 := by
  unfold cert13V11 cert13I11 cert13Q11 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V12 : P13 := 1 + X^2 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^12
def cert13I12 : P13 := 1 + X + X^4 + X^7 + X^8
def cert13Q12 : P13 := X + X^3 + X^5 + X^6 + X^7
lemma cert13InvPoly12 : cert13V12 * cert13I12 + 1 = f13 * cert13Q12 := by
  unfold cert13V12 cert13I12 cert13Q12 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V13 : P13 := 1 + X^2 + X^3 + X^5 + X^6 + X^9
def cert13I13 : P13 := X + X^2 + X^6 + X^7
def cert13Q13 : P13 := 1 + X^2 + X^3
lemma cert13InvPoly13 : cert13V13 * cert13I13 + 1 = f13 * cert13Q13 := by
  unfold cert13V13 cert13I13 cert13Q13 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V14 : P13 := X + X^3 + X^5 + X^8 + X^11
def cert13I14 : P13 := X^3 + X^4 + X^5 + X^7 + X^9 + X^10 + X^11
def cert13Q14 : P13 := 1 + X + X^2 + X^4 + X^6 + X^7 + X^8 + X^9
lemma cert13InvPoly14 : cert13V14 * cert13I14 + 1 = f13 * cert13Q14 := by
  unfold cert13V14 cert13I14 cert13Q14 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V15 : P13 := X + X^4 + X^5 + X^7 + X^10 + X^11 + X^12
def cert13I15 : P13 := X^2 + X^3 + X^5 + X^6 + X^8 + X^9
def cert13Q15 : P13 := 1 + X + X^2 + X^3 + X^8
lemma cert13InvPoly15 : cert13V15 * cert13I15 + 1 = f13 * cert13Q15 := by
  unfold cert13V15 cert13I15 cert13Q15 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V16 : P13 := X^2 + X^4 + X^5 + X^6 + X^9 + X^12
def cert13I16 : P13 := X + X^2 + X^4 + X^5 + X^7 + X^8 + X^10 + X^11 + X^12
def cert13Q16 : P13 := 1 + X + X^2 + X^3 + X^5 + X^8 + X^9 + X^10 + X^11
lemma cert13InvPoly16 : cert13V16 * cert13I16 + 1 = f13 * cert13Q16 := by
  unfold cert13V16 cert13I16 cert13Q16 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V17 : P13 := X^2 + X^3 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10
def cert13I17 : P13 := 1 + X + X^3 + X^4 + X^6 + X^7 + X^8 + X^10 + X^11
def cert13Q17 : P13 := 1 + X + X^3 + X^5 + X^8
lemma cert13InvPoly17 : cert13V17 * cert13I17 + 1 = f13 * cert13Q17 := by
  unfold cert13V17 cert13I17 cert13Q17 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V18 : P13 := 1 + X + X^3 + X^5 + X^7 + X^10 + X^11
def cert13I18 : P13 := 1 + X^2 + X^3 + X^5 + X^6 + X^8 + X^9 + X^10 + X^12
def cert13Q18 : P13 := X + X^3 + X^4 + X^5 + X^6 + X^8 + X^9 + X^10
lemma cert13InvPoly18 : cert13V18 * cert13I18 + 1 = f13 * cert13Q18 := by
  unfold cert13V18 cert13I18 cert13Q18 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V19 : P13 := 1 + X + X^4 + X^5 + X^8 + X^11 + X^12
def cert13I19 : P13 := 1 + X^5 + X^6 + X^8 + X^12
def cert13Q19 : P13 := X + X^2 + X^3 + X^4 + X^5 + X^6 + X^10 + X^11
lemma cert13InvPoly19 : cert13V19 * cert13I19 + 1 = f13 * cert13Q19 := by
  unfold cert13V19 cert13I19 cert13Q19 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V20 : P13 := 1 + X + X^2 + X^3 + X^5 + X^6 + X^7
def cert13I20 : P13 := X + X^2 + X^6 + X^9 + X^10 + X^11
def cert13Q20 : P13 := 1 + X^3 + X^5
lemma cert13InvPoly20 : cert13V20 * cert13I20 + 1 = f13 * cert13Q20 := by
  unfold cert13V20 cert13I20 cert13Q20 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V21 : P13 := 1 + X + X^2 + X^4 + X^5 + X^6 + X^8 + X^10 + X^12
def cert13I21 : P13 := 1 + X^3 + X^8 + X^9 + X^10 + X^12
def cert13Q21 : P13 := X + X^3 + X^5 + X^6 + X^7 + X^8 + X^11
lemma cert13InvPoly21 : cert13V21 * cert13I21 + 1 = f13 * cert13Q21 := by
  unfold cert13V21 cert13I21 cert13Q21 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V22 : P13 := X^4 + X^5 + X^9 + X^10 + X^11 + X^12
def cert13I22 : P13 := X^3 + X^7 + X^9 + X^10 + X^12
def cert13Q22 : P13 := 1 + X + X^2 + X^6 + X^8 + X^10 + X^11
lemma cert13InvPoly22 : cert13V22 * cert13I22 + 1 = f13 * cert13Q22 := by
  unfold cert13V22 cert13I22 cert13Q22 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V23 : P13 := X^3 + X^5 + X^7 + X^8 + X^9 + X^11
def cert13I23 : P13 := X^2 + X^3 + X^6 + X^7 + X^8
def cert13Q23 : P13 := 1 + X + X^2 + X^5 + X^6
lemma cert13InvPoly23 : cert13V23 * cert13I23 + 1 = f13 * cert13Q23 := by
  unfold cert13V23 cert13I23 cert13Q23 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V24 : P13 := X + X^3 + X^4 + X^8 + X^9 + X^10 + X^12
def cert13I24 : P13 := X + X^3 + X^4 + X^5 + X^7 + X^8 + X^10 + X^11
def cert13Q24 : P13 := 1 + X + X^3 + X^4 + X^6 + X^7 + X^8 + X^9 + X^10
lemma cert13InvPoly24 : cert13V24 * cert13I24 + 1 = f13 * cert13Q24 := by
  unfold cert13V24 cert13I24 cert13Q24 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V25 : P13 := X + X^7 + X^9
def cert13I25 : P13 := X^2 + X^4 + X^7 + X^8
def cert13Q25 : P13 := 1 + X + X^2 + X^3 + X^4
lemma cert13InvPoly25 : cert13V25 * cert13I25 + 1 = f13 * cert13Q25 := by
  unfold cert13V25 cert13I25 cert13Q25 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V26 : P13 := 1 + X^2 + X^6 + X^7 + X^8 + X^11
def cert13I26 : P13 := 1 + X^2 + X^6 + X^7 + X^9 + X^10 + X^12
def cert13Q26 : P13 := X^4 + X^5 + X^6 + X^8 + X^10
lemma cert13InvPoly26 : cert13V26 * cert13I26 + 1 = f13 * cert13Q26 := by
  unfold cert13V26 cert13I26 cert13Q26 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V27 : P13 := 1 + X^2 + X^3 + X^4 + X^6 + X^10 + X^11 + X^12
def cert13I27 : P13 := 1 + X + X^2 + X^4 + X^8 + X^10 + X^12
def cert13Q27 : P13 := X + X^2 + X^3 + X^6 + X^8 + X^10 + X^11
lemma cert13InvPoly27 : cert13V27 * cert13I27 + 1 = f13 * cert13Q27 := by
  unfold cert13V27 cert13I27 cert13Q27 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V28 : P13 := 1 + X^7 + X^8 + X^10
def cert13I28 : P13 := 1 + X + X^2 + X^3 + X^5 + X^7 + X^9
def cert13Q28 : P13 := X + X^3 + X^6
lemma cert13InvPoly28 : cert13V28 * cert13I28 + 1 = f13 * cert13Q28 := by
  unfold cert13V28 cert13I28 cert13Q28 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V29 : P13 := 1 + X^3 + X^4 + X^12
def cert13I29 : P13 := 1 + X^2 + X^4 + X^8 + X^9 + X^11 + X^12
def cert13Q29 : P13 := X^2 + X^7 + X^8 + X^10 + X^11
lemma cert13InvPoly29 : cert13V29 * cert13I29 + 1 = f13 * cert13Q29 := by
  unfold cert13V29 cert13I29 cert13Q29 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V30 : P13 := X + X^2 + X^3 + X^4 + X^6 + X^8 + X^9 + X^11 + X^12
def cert13I30 : P13 := X + X^5 + X^6 + X^9 + X^12
def cert13Q30 : P13 := 1 + X + X^4 + X^5 + X^10 + X^11
lemma cert13InvPoly30 : cert13V30 * cert13I30 + 1 = f13 * cert13Q30 := by
  unfold cert13V30 cert13I30 cert13Q30 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
def cert13V31 : P13 := X + X^2 + X^6 + X^7 + X^9 + X^10 + X^11
def cert13I31 : P13 := X^2 + X^5 + X^7 + X^8 + X^9 + X^12
def cert13Q31 : P13 := 1 + X + X^2 + X^3 + X^6 + X^7 + X^8 + X^9 + X^10
lemma cert13InvPoly31 : cert13V31 * cert13I31 + 1 = f13 * cert13Q31 := by
  unfold cert13V31 cert13I31 cert13Q31 f13
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
#print axioms cert13InvPoly01
#print axioms cert13InvPoly31

local instance : CharP (AdjoinRoot f13) 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f13)).injective 2
theorem cert13InvAdjoin_of_poly {v i q : P13} (h : v * i + 1 = f13 * q) :
    (AdjoinRoot.mk f13 v) * (AdjoinRoot.mk f13 i) = 1 := by
  have hd : f13 ∣ v * i + 1 := ⟨q, h⟩
  have hz : AdjoinRoot.mk f13 (v * i + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f13 v) * (AdjoinRoot.mk f13 i) + 1 = 0 := by
    simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f13 v) * (AdjoinRoot.mk f13 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : AdjoinRoot f13) + 1 = 0 := by
        calc
          (1 : AdjoinRoot f13) + 1 = (2 : AdjoinRoot f13) := by norm_num
          _ = 0 := CharP.cast_eq_zero (AdjoinRoot f13) 2
      exact neg_eq_of_add_eq_zero_left ht
theorem cert13InvAdjoin01 : (AdjoinRoot.mk f13 cert13V01) * (AdjoinRoot.mk f13 cert13I01) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly01
theorem cert13InvAdjoin02 : (AdjoinRoot.mk f13 cert13V02) * (AdjoinRoot.mk f13 cert13I02) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly02
theorem cert13InvAdjoin03 : (AdjoinRoot.mk f13 cert13V03) * (AdjoinRoot.mk f13 cert13I03) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly03
theorem cert13InvAdjoin04 : (AdjoinRoot.mk f13 cert13V04) * (AdjoinRoot.mk f13 cert13I04) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly04
theorem cert13InvAdjoin05 : (AdjoinRoot.mk f13 cert13V05) * (AdjoinRoot.mk f13 cert13I05) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly05
theorem cert13InvAdjoin06 : (AdjoinRoot.mk f13 cert13V06) * (AdjoinRoot.mk f13 cert13I06) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly06
theorem cert13InvAdjoin07 : (AdjoinRoot.mk f13 cert13V07) * (AdjoinRoot.mk f13 cert13I07) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly07
theorem cert13InvAdjoin08 : (AdjoinRoot.mk f13 cert13V08) * (AdjoinRoot.mk f13 cert13I08) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly08
theorem cert13InvAdjoin09 : (AdjoinRoot.mk f13 cert13V09) * (AdjoinRoot.mk f13 cert13I09) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly09
theorem cert13InvAdjoin10 : (AdjoinRoot.mk f13 cert13V10) * (AdjoinRoot.mk f13 cert13I10) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly10
theorem cert13InvAdjoin11 : (AdjoinRoot.mk f13 cert13V11) * (AdjoinRoot.mk f13 cert13I11) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly11
theorem cert13InvAdjoin12 : (AdjoinRoot.mk f13 cert13V12) * (AdjoinRoot.mk f13 cert13I12) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly12
theorem cert13InvAdjoin13 : (AdjoinRoot.mk f13 cert13V13) * (AdjoinRoot.mk f13 cert13I13) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly13
theorem cert13InvAdjoin14 : (AdjoinRoot.mk f13 cert13V14) * (AdjoinRoot.mk f13 cert13I14) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly14
theorem cert13InvAdjoin15 : (AdjoinRoot.mk f13 cert13V15) * (AdjoinRoot.mk f13 cert13I15) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly15
theorem cert13InvAdjoin16 : (AdjoinRoot.mk f13 cert13V16) * (AdjoinRoot.mk f13 cert13I16) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly16
theorem cert13InvAdjoin17 : (AdjoinRoot.mk f13 cert13V17) * (AdjoinRoot.mk f13 cert13I17) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly17
theorem cert13InvAdjoin18 : (AdjoinRoot.mk f13 cert13V18) * (AdjoinRoot.mk f13 cert13I18) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly18
theorem cert13InvAdjoin19 : (AdjoinRoot.mk f13 cert13V19) * (AdjoinRoot.mk f13 cert13I19) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly19
theorem cert13InvAdjoin20 : (AdjoinRoot.mk f13 cert13V20) * (AdjoinRoot.mk f13 cert13I20) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly20
theorem cert13InvAdjoin21 : (AdjoinRoot.mk f13 cert13V21) * (AdjoinRoot.mk f13 cert13I21) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly21
theorem cert13InvAdjoin22 : (AdjoinRoot.mk f13 cert13V22) * (AdjoinRoot.mk f13 cert13I22) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly22
theorem cert13InvAdjoin23 : (AdjoinRoot.mk f13 cert13V23) * (AdjoinRoot.mk f13 cert13I23) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly23
theorem cert13InvAdjoin24 : (AdjoinRoot.mk f13 cert13V24) * (AdjoinRoot.mk f13 cert13I24) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly24
theorem cert13InvAdjoin25 : (AdjoinRoot.mk f13 cert13V25) * (AdjoinRoot.mk f13 cert13I25) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly25
theorem cert13InvAdjoin26 : (AdjoinRoot.mk f13 cert13V26) * (AdjoinRoot.mk f13 cert13I26) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly26
theorem cert13InvAdjoin27 : (AdjoinRoot.mk f13 cert13V27) * (AdjoinRoot.mk f13 cert13I27) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly27
theorem cert13InvAdjoin28 : (AdjoinRoot.mk f13 cert13V28) * (AdjoinRoot.mk f13 cert13I28) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly28
theorem cert13InvAdjoin29 : (AdjoinRoot.mk f13 cert13V29) * (AdjoinRoot.mk f13 cert13I29) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly29
theorem cert13InvAdjoin30 : (AdjoinRoot.mk f13 cert13V30) * (AdjoinRoot.mk f13 cert13I30) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly30
theorem cert13InvAdjoin31 : (AdjoinRoot.mk f13 cert13V31) * (AdjoinRoot.mk f13 cert13I31) = 1 := by
  exact cert13InvAdjoin_of_poly cert13InvPoly31
theorem cert13_inverse_representatives_sum : cert13I01 + cert13I02 + cert13I03 + cert13I04 + cert13I05 + cert13I06 + cert13I07 + cert13I08 + cert13I09 + cert13I10 + cert13I11 + cert13I12 + cert13I13 + cert13I14 + cert13I15 + cert13I16 + cert13I17 + cert13I18 + cert13I19 + cert13I20 + cert13I21 + cert13I22 + cert13I23 + cert13I24 + cert13I25 + cert13I26 + cert13I27 + cert13I28 + cert13I29 + cert13I30 + cert13I31 = 0 := by
  unfold cert13I01 cert13I02 cert13I03 cert13I04 cert13I05 cert13I06 cert13I07 cert13I08 cert13I09 cert13I10 cert13I11 cert13I12 cert13I13 cert13I14 cert13I15 cert13I16 cert13I17 cert13I18 cert13I19 cert13I20 cert13I21 cert13I22 cert13I23 cert13I24 cert13I25 cert13I26 cert13I27 cert13I28 cert13I29 cert13I30 cert13I31
  ring_nf
  simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem cert13_inverse_sum_adjoin : AdjoinRoot.mk f13 cert13I01 + AdjoinRoot.mk f13 cert13I02 + AdjoinRoot.mk f13 cert13I03 + AdjoinRoot.mk f13 cert13I04 + AdjoinRoot.mk f13 cert13I05 + AdjoinRoot.mk f13 cert13I06 + AdjoinRoot.mk f13 cert13I07 + AdjoinRoot.mk f13 cert13I08 + AdjoinRoot.mk f13 cert13I09 + AdjoinRoot.mk f13 cert13I10 + AdjoinRoot.mk f13 cert13I11 + AdjoinRoot.mk f13 cert13I12 + AdjoinRoot.mk f13 cert13I13 + AdjoinRoot.mk f13 cert13I14 + AdjoinRoot.mk f13 cert13I15 + AdjoinRoot.mk f13 cert13I16 + AdjoinRoot.mk f13 cert13I17 + AdjoinRoot.mk f13 cert13I18 + AdjoinRoot.mk f13 cert13I19 + AdjoinRoot.mk f13 cert13I20 + AdjoinRoot.mk f13 cert13I21 + AdjoinRoot.mk f13 cert13I22 + AdjoinRoot.mk f13 cert13I23 + AdjoinRoot.mk f13 cert13I24 + AdjoinRoot.mk f13 cert13I25 + AdjoinRoot.mk f13 cert13I26 + AdjoinRoot.mk f13 cert13I27 + AdjoinRoot.mk f13 cert13I28 + AdjoinRoot.mk f13 cert13I29 + AdjoinRoot.mk f13 cert13I30 + AdjoinRoot.mk f13 cert13I31 = 0 := by
  have h := congrArg (AdjoinRoot.mk f13) cert13_inverse_representatives_sum
  simpa only [map_add, map_zero] using h
#print axioms cert13_inverse_representatives_sum
#print axioms cert13_inverse_sum_adjoin
