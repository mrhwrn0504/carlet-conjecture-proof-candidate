import Carlet.N13InverseProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
set_option linter.unusedSimpArgs false
namespace Carlet

def n13K4Base0 : P13 := 1
def n13K4Base1 : P13 := X^3 + X^4
def n13K4Base2 : P13 := X^6 + X^8
def n13K4Base3 : P13 := X^1 + X^2 + X^4 + X^5 + X^11
def n13K4BasePoly : Fin 4 → P13
| 0 => n13K4Base0
| 1 => n13K4Base1
| 2 => n13K4Base2
| 3 => n13K4Base3

def n13K4P01 : P13 := 1
def n13K4I01 : P13 := 1
def n13K4Q01 : P13 := 0
lemma n13K4InvPoly01 : n13K4P01 * n13K4I01 + 1 = f13 * n13K4Q01 := by
  unfold n13K4P01 n13K4I01 n13K4Q01 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin01 : (AdjoinRoot.mk f13 n13K4P01) * (AdjoinRoot.mk f13 n13K4I01) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly01

def n13K4P02 : P13 := X^3 + X^4
def n13K4I02 : P13 := X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^11
def n13K4Q02 : P13 := 1 + X^1 + X^2
lemma n13K4InvPoly02 : n13K4P02 * n13K4I02 + 1 = f13 * n13K4Q02 := by
  unfold n13K4P02 n13K4I02 n13K4Q02 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin02 : (AdjoinRoot.mk f13 n13K4P02) * (AdjoinRoot.mk f13 n13K4I02) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly02

def n13K4P03 : P13 := 1 + X^3 + X^4
def n13K4I03 : P13 := 1 + X^1 + X^4 + X^5 + X^6 + X^7 + X^11
def n13K4Q03 : P13 := X^1 + X^2
lemma n13K4InvPoly03 : n13K4P03 * n13K4I03 + 1 = f13 * n13K4Q03 := by
  unfold n13K4P03 n13K4I03 n13K4Q03 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin03 : (AdjoinRoot.mk f13 n13K4P03) * (AdjoinRoot.mk f13 n13K4I03) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly03

def n13K4P04 : P13 := X^6 + X^8
def n13K4I04 : P13 := 1 + X^2 + X^4 + X^6 + X^7
def n13K4Q04 : P13 := 1 + X^1 + X^2
lemma n13K4InvPoly04 : n13K4P04 * n13K4I04 + 1 = f13 * n13K4Q04 := by
  unfold n13K4P04 n13K4I04 n13K4Q04 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin04 : (AdjoinRoot.mk f13 n13K4P04) * (AdjoinRoot.mk f13 n13K4I04) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly04

def n13K4P05 : P13 := 1 + X^6 + X^8
def n13K4I05 : P13 := X^3 + X^5 + X^8 + X^9
def n13K4Q05 : P13 := 1 + X^1 + X^2 + X^3 + X^4
lemma n13K4InvPoly05 : n13K4P05 * n13K4I05 + 1 = f13 * n13K4Q05 := by
  unfold n13K4P05 n13K4I05 n13K4Q05 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin05 : (AdjoinRoot.mk f13 n13K4P05) * (AdjoinRoot.mk f13 n13K4I05) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly05

def n13K4P06 : P13 := X^3 + X^4 + X^6 + X^8
def n13K4I06 : P13 := 1 + X^1 + X^3 + X^8 + X^9
def n13K4Q06 : P13 := 1 + X^1 + X^2 + X^3 + X^4
lemma n13K4InvPoly06 : n13K4P06 * n13K4I06 + 1 = f13 * n13K4Q06 := by
  unfold n13K4P06 n13K4I06 n13K4Q06 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin06 : (AdjoinRoot.mk f13 n13K4P06) * (AdjoinRoot.mk f13 n13K4I06) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly06

def n13K4P07 : P13 := 1 + X^3 + X^4 + X^6 + X^8
def n13K4I07 : P13 := X^1 + X^3 + X^5 + X^6 + X^7 + X^10 + X^12
def n13K4Q07 : P13 := 1 + X^7
lemma n13K4InvPoly07 : n13K4P07 * n13K4I07 + 1 = f13 * n13K4Q07 := by
  unfold n13K4P07 n13K4I07 n13K4Q07 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin07 : (AdjoinRoot.mk f13 n13K4P07) * (AdjoinRoot.mk f13 n13K4I07) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly07

def n13K4P08 : P13 := X^1 + X^2 + X^4 + X^5 + X^11
def n13K4I08 : P13 := 1 + X^2 + X^3 + X^5 + X^6 + X^10
def n13K4Q08 : P13 := 1 + X^2 + X^3 + X^4 + X^8
lemma n13K4InvPoly08 : n13K4P08 * n13K4I08 + 1 = f13 * n13K4Q08 := by
  unfold n13K4P08 n13K4I08 n13K4Q08 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin08 : (AdjoinRoot.mk f13 n13K4P08) * (AdjoinRoot.mk f13 n13K4I08) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly08

def n13K4P09 : P13 := 1 + X^1 + X^2 + X^4 + X^5 + X^11
def n13K4I09 : P13 := 1 + X^4 + X^6 + X^10
def n13K4Q09 : P13 := X^1 + X^4 + X^8
lemma n13K4InvPoly09 : n13K4P09 * n13K4I09 + 1 = f13 * n13K4Q09 := by
  unfold n13K4P09 n13K4I09 n13K4Q09 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin09 : (AdjoinRoot.mk f13 n13K4P09) * (AdjoinRoot.mk f13 n13K4I09) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly09

def n13K4P10 : P13 := X^1 + X^2 + X^3 + X^5 + X^11
def n13K4I10 : P13 := X^2 + X^3 + X^4 + X^5 + X^8 + X^10 + X^12
def n13K4Q10 : P13 := 1 + X^1 + X^2 + X^3 + X^4 + X^6 + X^8 + X^10
lemma n13K4InvPoly10 : n13K4P10 * n13K4I10 + 1 = f13 * n13K4Q10 := by
  unfold n13K4P10 n13K4I10 n13K4Q10 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin10 : (AdjoinRoot.mk f13 n13K4P10) * (AdjoinRoot.mk f13 n13K4I10) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly10

def n13K4P11 : P13 := 1 + X^1 + X^2 + X^3 + X^5 + X^11
def n13K4I11 : P13 := X^1 + X^6 + X^9 + X^10 + X^11
def n13K4Q11 : P13 := 1 + X^2 + X^3 + X^4 + X^7 + X^8 + X^9
lemma n13K4InvPoly11 : n13K4P11 * n13K4I11 + 1 = f13 * n13K4Q11 := by
  unfold n13K4P11 n13K4I11 n13K4Q11 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin11 : (AdjoinRoot.mk f13 n13K4P11) * (AdjoinRoot.mk f13 n13K4I11) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly11

def n13K4P12 : P13 := X^1 + X^2 + X^4 + X^5 + X^6 + X^8 + X^11
def n13K4I12 : P13 := 1 + X^1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^8 + X^10
def n13K4Q12 : P13 := 1 + X^3 + X^4 + X^5 + X^6 + X^8
lemma n13K4InvPoly12 : n13K4P12 * n13K4I12 + 1 = f13 * n13K4Q12 := by
  unfold n13K4P12 n13K4I12 n13K4Q12 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin12 : (AdjoinRoot.mk f13 n13K4P12) * (AdjoinRoot.mk f13 n13K4I12) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly12

def n13K4P13 : P13 := 1 + X^1 + X^2 + X^4 + X^5 + X^6 + X^8 + X^11
def n13K4I13 : P13 := 1 + X^3 + X^4 + X^6 + X^7 + X^8
def n13K4Q13 : P13 := X^1 + X^3 + X^4 + X^5 + X^6
lemma n13K4InvPoly13 : n13K4P13 * n13K4I13 + 1 = f13 * n13K4Q13 := by
  unfold n13K4P13 n13K4I13 n13K4Q13 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin13 : (AdjoinRoot.mk f13 n13K4P13) * (AdjoinRoot.mk f13 n13K4I13) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly13

def n13K4P14 : P13 := X^1 + X^2 + X^3 + X^5 + X^6 + X^8 + X^11
def n13K4I14 : P13 := X^1 + X^2 + X^3 + X^5 + X^9 + X^10 + X^11
def n13K4Q14 : P13 := 1 + X^1 + X^3 + X^5 + X^6 + X^7 + X^8 + X^9
lemma n13K4InvPoly14 : n13K4P14 * n13K4I14 + 1 = f13 * n13K4Q14 := by
  unfold n13K4P14 n13K4I14 n13K4Q14 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin14 : (AdjoinRoot.mk f13 n13K4P14) * (AdjoinRoot.mk f13 n13K4I14) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly14

def n13K4P15 : P13 := 1 + X^1 + X^2 + X^3 + X^5 + X^6 + X^8 + X^11
def n13K4I15 : P13 := X^2 + X^3 + X^4 + X^6 + X^7 + X^9 + X^10
def n13K4Q15 : P13 := 1 + X^1 + X^3 + X^7 + X^8
lemma n13K4InvPoly15 : n13K4P15 * n13K4I15 + 1 = f13 * n13K4Q15 := by
  unfold n13K4P15 n13K4I15 n13K4Q15 f13
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InvAdjoin15 : (AdjoinRoot.mk f13 n13K4P15) * (AdjoinRoot.mk f13 n13K4I15) = 1 := by
  exact cert13InvAdjoin_of_poly n13K4InvPoly15

theorem n13K4InverseRepresentatives_sum_zero : n13K4I01 + n13K4I02 + n13K4I03 + n13K4I04 + n13K4I05 + n13K4I06 + n13K4I07 + n13K4I08 + n13K4I09 + n13K4I10 + n13K4I11 + n13K4I12 + n13K4I13 + n13K4I14 + n13K4I15 = 0 := by
  unfold n13K4I01 n13K4I02 n13K4I03 n13K4I04 n13K4I05 n13K4I06 n13K4I07 n13K4I08 n13K4I09 n13K4I10 n13K4I11 n13K4I12 n13K4I13 n13K4I14 n13K4I15
  ring_nf
  simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
theorem n13K4InverseSumAdjoin : AdjoinRoot.mk f13 n13K4I01 + AdjoinRoot.mk f13 n13K4I02 + AdjoinRoot.mk f13 n13K4I03 + AdjoinRoot.mk f13 n13K4I04 + AdjoinRoot.mk f13 n13K4I05 + AdjoinRoot.mk f13 n13K4I06 + AdjoinRoot.mk f13 n13K4I07 + AdjoinRoot.mk f13 n13K4I08 + AdjoinRoot.mk f13 n13K4I09 + AdjoinRoot.mk f13 n13K4I10 + AdjoinRoot.mk f13 n13K4I11 + AdjoinRoot.mk f13 n13K4I12 + AdjoinRoot.mk f13 n13K4I13 + AdjoinRoot.mk f13 n13K4I14 + AdjoinRoot.mk f13 n13K4I15 = 0 := by
  have h := congrArg (AdjoinRoot.mk f13) n13K4InverseRepresentatives_sum_zero
  simpa only [map_add, map_zero] using h
#print axioms n13K4InvPoly01
#print axioms n13K4InvAdjoin01
#print axioms n13K4InverseRepresentatives_sum_zero
#print axioms n13K4InverseSumAdjoin

end Carlet
