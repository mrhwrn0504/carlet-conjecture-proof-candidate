import Carlet.Frobenius23Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def n23FourT : P17 := X^3 + X^4
def n23FourU : P17 := X^3 + X^4 + X^6 + X^8
def n23FourD : P17 := 1 + X^1 + X^3 + X^4 + X^8 + X^9 + X^10 + X^11 + X^15 + X^18 + X^19 + X^22
def n23FourZ : P17 := X^1 + X^2 + X^3 + X^5 + X^7 + X^9 + X^10 + X^11 + X^12 + X^13 + X^16 + X^18 + X^19 + X^20 + X^21
def n23FourS : P17 := X^1 + X^3 + X^6 + X^8 + X^11 + X^12 + X^15 + X^18 + X^19 + X^21
def n23FourV : P17 := X^4 + X^5 + X^8 + X^11 + X^13 + X^16 + X^18 + X^20
def n23FourIU : P17 := 1 + X^1 + X^4 + X^5 + X^7 + X^8 + X^11 + X^13 + X^18 + X^19 + X^21
def n23FourIU1 : P17 := 1 + X^2 + X^3 + X^7 + X^10 + X^11 + X^12 + X^15 + X^17 + X^18 + X^21 + X^22
private theorem n23FourZSquare : n23FourZ^2 = (X^2 + X^4 + X^6 + X^10 + X^14 + X^18 + X^20 + X^22 + X^24 + X^26 + X^32 + X^36 + X^38 + X^40 + X^42 : P17) := by
  unfold n23FourZ
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n23FourSSquare : n23FourS^2 = (X^2 + X^6 + X^12 + X^16 + X^22 + X^24 + X^30 + X^36 + X^38 + X^42 : P17) := by
  unfold n23FourS
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n23FourVSquare : n23FourV^2 = (X^8 + X^10 + X^16 + X^22 + X^26 + X^32 + X^36 + X^40 : P17) := by
  unfold n23FourV
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n23FourUProduct : n23FourU*(n23FourU+1) = (X^3 + X^4 + X^12 + X^16 : P17) := by
  unfold n23FourU
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQUeq : P17 := 0
theorem n23FourPolyUeq : n23FourT^2+n23FourT+n23FourU = f23*n23FourQUeq := by
  unfold n23FourT n23FourU n23FourQUeq f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQUinv : P17 := 1 + X^3 + X^6
theorem n23FourPolyUinv : n23FourU*n23FourIU+1 = f23*n23FourQUinv := by
  unfold n23FourU n23FourIU n23FourQUinv f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQU1inv : P17 := X^2 + X^4 + X^5 + X^6 + X^7
theorem n23FourPolyU1inv : (n23FourU+1)*n23FourIU1+1 = f23*n23FourQU1inv := by
  unfold n23FourU n23FourIU1 n23FourQU1inv f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQDeq : P17 := X^1
theorem n23FourPolyDeq : n23FourU^3+n23FourU+1+n23FourD = f23*n23FourQDeq := by
  unfold n23FourU n23FourD n23FourQDeq f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQZeq : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^7 + X^9 + X^12 + X^15 + X^16 + X^17 + X^21 + X^22 + X^23 + X^24 + X^25 + X^27 + X^29 + X^33 + X^36 + X^38 + X^39 + X^41
theorem n23FourPolyZeq : n23FourD*(n23FourZ^2+n23FourZ)+1 = f23*n23FourQZeq := by
  rw [n23FourZSquare]
  unfold n23FourD n23FourZ n23FourQZeq f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQSeq : P17 := X^1 + X^2 + X^3 + X^4 + X^6 + X^8 + X^10 + X^11 + X^12 + X^14 + X^15 + X^19
theorem n23FourPolySeq : n23FourS^2+n23FourS+n23FourU*(n23FourU+1)*n23FourZ = f23*n23FourQSeq := by
  rw [n23FourSSquare, n23FourUProduct]
  unfold n23FourS n23FourZ n23FourQSeq f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n23FourQVeq : P17 := X^6 + X^9 + X^13 + X^17
theorem n23FourPolyVeq : n23FourV^2+n23FourV+n23FourU*n23FourS = f23*n23FourQVeq := by
  rw [n23FourVSquare]
  unfold n23FourV n23FourU n23FourS n23FourQVeq f23
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms n23FourPolyZeq
#print axioms n23FourPolySeq
#print axioms n23FourPolyVeq
