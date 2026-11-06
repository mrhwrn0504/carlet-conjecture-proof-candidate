import Carlet.Frobenius25Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def n25FourT : P17 := X^1 + X^2 + X^3 + X^4 + X^6
def n25FourU : P17 := X^1 + X^3 + X^8 + X^12
def n25FourD : P17 := X^1 + X^2 + X^6 + X^8 + X^9 + X^11 + X^12 + X^14 + X^17 + X^18 + X^19 + X^24
def n25FourZ : P17 := X^1 + X^4 + X^5 + X^6 + X^7 + X^8 + X^11 + X^12 + X^13 + X^15 + X^17 + X^22 + X^23
def n25FourS : P17 := X^2 + X^3 + X^7 + X^8 + X^9 + X^13 + X^14 + X^15 + X^17 + X^19 + X^20 + X^21 + X^23
def n25FourV : P17 := X^1 + X^2 + X^4 + X^11 + X^13 + X^15 + X^16 + X^17 + X^21 + X^22
def n25FourIU : P17 := 1 + X^5 + X^9 + X^10 + X^11 + X^17 + X^18 + X^19 + X^22 + X^24
def n25FourIU1 : P17 := 1 + X^1 + X^4 + X^5 + X^7 + X^8 + X^9 + X^15 + X^16 + X^17 + X^21 + X^22
private theorem n25FourZSquare : n25FourZ^2 = (X^2 + X^8 + X^10 + X^12 + X^14 + X^16 + X^22 + X^24 + X^26 + X^30 + X^34 + X^44 + X^46 : P17) := by
  unfold n25FourZ
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n25FourSSquare : n25FourS^2 = (X^4 + X^6 + X^14 + X^16 + X^18 + X^26 + X^28 + X^30 + X^34 + X^38 + X^40 + X^42 + X^46 : P17) := by
  unfold n25FourS
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n25FourVSquare : n25FourV^2 = (X^2 + X^4 + X^8 + X^22 + X^26 + X^30 + X^32 + X^34 + X^42 + X^44 : P17) := by
  unfold n25FourV
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n25FourUProduct : n25FourU*(n25FourU+1) = (X^1 + X^2 + X^3 + X^6 + X^8 + X^12 + X^16 + X^24 : P17) := by
  unfold n25FourU
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQUeq : P17 := 0
theorem n25FourPolyUeq : n25FourT^2+n25FourT+n25FourU = f25*n25FourQUeq := by
  unfold n25FourT n25FourU n25FourQUeq f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQUinv : P17 := 1 + X^1 + X^4 + X^6 + X^7 + X^9 + X^11
theorem n25FourPolyUinv : n25FourU*n25FourIU+1 = f25*n25FourQUinv := by
  unfold n25FourU n25FourIU n25FourQUinv f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQU1inv : P17 := X^2 + X^3 + X^5 + X^8 + X^9
theorem n25FourPolyU1inv : (n25FourU+1)*n25FourIU1+1 = f25*n25FourQU1inv := by
  unfold n25FourU n25FourIU1 n25FourQU1inv f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQDeq : P17 := 1 + X^2 + X^3 + X^7 + X^11
theorem n25FourPolyDeq : n25FourU^3+n25FourU+1+n25FourD = f25*n25FourQDeq := by
  unfold n25FourU n25FourD n25FourQDeq f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQZeq : P17 := 1 + X^2 + X^3 + X^4 + X^6 + X^8 + X^9 + X^10 + X^13 + X^17 + X^18 + X^21 + X^22 + X^23 + X^24 + X^26 + X^27 + X^31 + X^32 + X^33 + X^35 + X^36 + X^37 + X^39 + X^40 + X^43 + X^45
theorem n25FourPolyZeq : n25FourD*(n25FourZ^2+n25FourZ)+1 = f25*n25FourQZeq := by
  rw [n25FourZSquare]
  unfold n25FourD n25FourZ n25FourQZeq f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQSeq : P17 := X^5 + X^6 + X^7 + X^8 + X^11 + X^12 + X^15 + X^16 + X^17 + X^22
theorem n25FourPolySeq : n25FourS^2+n25FourS+n25FourU*(n25FourU+1)*n25FourZ = f25*n25FourQSeq := by
  rw [n25FourSSquare, n25FourUProduct]
  unfold n25FourS n25FourZ n25FourQSeq f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n25FourQVeq : P17 := X^1 + X^3 + X^5 + X^8 + X^9 + X^10 + X^17 + X^19
theorem n25FourPolyVeq : n25FourV^2+n25FourV+n25FourU*n25FourS = f25*n25FourQVeq := by
  rw [n25FourVSquare]
  unfold n25FourV n25FourU n25FourS n25FourQVeq f25
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms n25FourPolyZeq
#print axioms n25FourPolySeq
#print axioms n25FourPolyVeq
