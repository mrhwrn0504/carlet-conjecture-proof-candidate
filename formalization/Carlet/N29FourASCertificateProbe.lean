import Carlet.Frobenius29Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def n29FourT : P17 := X^2 + X^5
def n29FourU : P17 := X^2 + X^4 + X^5 + X^10
def n29FourD : P17 := 1 + X^1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^8 + X^9 + X^13 + X^15 + X^18 + X^20 + X^22 + X^24 + X^25
def n29FourZ : P17 := X^2 + X^3 + X^4 + X^5 + X^6 + X^9 + X^10 + X^11 + X^12 + X^15 + X^17 + X^20 + X^21 + X^22 + X^23 + X^25 + X^26
def n29FourS : P17 := 1 + X^1 + X^4 + X^6 + X^8 + X^10 + X^14 + X^17 + X^19 + X^20 + X^21 + X^22 + X^25 + X^27
def n29FourV : P17 := 1 + X^1 + X^3 + X^4 + X^5 + X^7 + X^8 + X^9 + X^10 + X^11 + X^14 + X^15 + X^16 + X^18 + X^19 + X^21 + X^22 + X^23 + X^25 + X^27 + X^28
def n29FourIU : P17 := 1 + X^1 + X^3 + X^4 + X^6 + X^11 + X^12 + X^13 + X^14 + X^17 + X^21 + X^22 + X^23 + X^25 + X^26
def n29FourIU1 : P17 := X^3 + X^5 + X^6 + X^7 + X^8 + X^15 + X^16 + X^19 + X^23 + X^24 + X^27
private theorem n29FourZSquare : n29FourZ^2 = (X^4 + X^6 + X^8 + X^10 + X^12 + X^18 + X^20 + X^22 + X^24 + X^30 + X^34 + X^40 + X^42 + X^44 + X^46 + X^50 + X^52 : P17) := by
  unfold n29FourZ
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n29FourSSquare : n29FourS^2 = (1 + X^2 + X^8 + X^12 + X^16 + X^20 + X^28 + X^34 + X^38 + X^40 + X^42 + X^44 + X^50 + X^54 : P17) := by
  unfold n29FourS
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n29FourVSquare : n29FourV^2 = (1 + X^2 + X^6 + X^8 + X^10 + X^14 + X^16 + X^18 + X^20 + X^22 + X^28 + X^30 + X^32 + X^36 + X^38 + X^42 + X^44 + X^46 + X^50 + X^54 + X^56 : P17) := by
  unfold n29FourV
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
private theorem n29FourUProduct : n29FourU*(n29FourU+1) = (X^2 + X^5 + X^8 + X^20 : P17) := by
  unfold n29FourU
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQUeq : P17 := 0
theorem n29FourPolyUeq : n29FourT^2+n29FourT+n29FourU = f29*n29FourQUeq := by
  unfold n29FourT n29FourU n29FourQUeq f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQUinv : P17 := 1 + X^3 + X^4 + X^6 + X^7
theorem n29FourPolyUinv : n29FourU*n29FourIU+1 = f29*n29FourQUinv := by
  unfold n29FourU n29FourIU n29FourQUinv f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQU1inv : P17 := 1 + X^2 + X^3 + X^4 + X^5 + X^8
theorem n29FourPolyU1inv : (n29FourU+1)*n29FourIU1+1 = f29*n29FourQU1inv := by
  unfold n29FourU n29FourIU1 n29FourQU1inv f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQDeq : P17 := X^1
theorem n29FourPolyDeq : n29FourU^3+n29FourU+1+n29FourD = f29*n29FourQDeq := by
  unfold n29FourU n29FourD n29FourQDeq f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQZeq : P17 := 1 + X^5 + X^6 + X^8 + X^10 + X^12 + X^14 + X^16 + X^18 + X^20 + X^25 + X^27 + X^28 + X^31 + X^33 + X^34 + X^36 + X^37 + X^39 + X^40 + X^41 + X^42 + X^46 + X^47 + X^48
theorem n29FourPolyZeq : n29FourD*(n29FourZ^2+n29FourZ)+1 = f29*n29FourQZeq := by
  rw [n29FourZSquare]
  unfold n29FourD n29FourZ n29FourQZeq f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQSeq : P17 := X^1 + X^2 + X^3 + X^4 + X^6 + X^8 + X^9 + X^12 + X^14 + X^15 + X^16 + X^17 + X^21 + X^25
theorem n29FourPolySeq : n29FourS^2+n29FourS+n29FourU*(n29FourU+1)*n29FourZ = f29*n29FourQSeq := by
  rw [n29FourSSquare, n29FourUProduct]
  unfold n29FourS n29FourZ n29FourQSeq f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
def n29FourQVeq : P17 := X^1 + X^3 + X^6 + X^7 + X^8 + X^9 + X^13 + X^15 + X^17 + X^21 + X^25 + X^27
theorem n29FourPolyVeq : n29FourV^2+n29FourV+n29FourU*n29FourS = f29*n29FourQVeq := by
  rw [n29FourVSquare]
  unfold n29FourV n29FourU n29FourS n29FourQVeq f29
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
#print axioms n29FourPolyZeq
#print axioms n29FourPolySeq
#print axioms n29FourPolyVeq
