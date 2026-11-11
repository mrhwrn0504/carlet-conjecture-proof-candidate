import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
def f29 : P17 := X^29 + X^2 + 1
def r29_0 : P17 := X^1
def r29_1 : P17 := X^2
def r29_2 : P17 := X^4
def r29_3 : P17 := X^8
def r29_4 : P17 := X^16
def r29_5 : P17 := X^3 + X^5
def r29_6 : P17 := X^6 + X^10
def r29_7 : P17 := X^12 + X^20
def r29_8 : P17 := X^11 + X^13 + X^24
def r29_9 : P17 := X^19 + X^21 + X^22 + X^26
def r29_10 : P17 := X^9 + X^11 + X^13 + X^17 + X^23 + X^25
def r29_11 : P17 := X^5 + X^7 + X^17 + X^18 + X^19 + X^21 + X^22 + X^23 + X^26
def r29_12 : P17 := X^5 + X^10 + X^11 + X^13 + X^14 + X^19 + X^23 + X^25
def r29_13 : P17 := X^9 + X^10 + X^11 + X^17 + X^19 + X^20 + X^21 + X^22 + X^23 + X^26 + X^28
def r29_14 : P17 := 1 + X^2 + X^5 + X^7 + X^9 + X^18 + X^19 + X^20 + X^22 + X^23 + X^25 + X^27
def r29_15 : P17 := 1 + X^4 + X^7 + X^10 + X^13 + X^14 + X^15 + X^18 + X^19 + X^21 + X^23 + X^25 + X^27
def r29_16 : P17 := 1 + X^1 + X^3 + X^7 + X^8 + X^11 + X^13 + X^14 + X^15 + X^17 + X^19 + X^20 + X^21 + X^23 + X^25 + X^26 + X^27 + X^28
def r29_17 : P17 := X^1 + X^3 + X^5 + X^6 + X^7 + X^9 + X^14 + X^15 + X^16 + X^17 + X^19 + X^21 + X^22 + X^26 + X^28
def r29_18 : P17 := 1 + X^1 + X^6 + X^7 + X^9 + X^10 + X^11 + X^12 + X^13 + X^14 + X^17 + X^18 + X^23 + X^25 + X^27 + X^28
def r29_19 : P17 := X^5 + X^9 + X^12 + X^14 + X^17 + X^18 + X^19 + X^20 + X^21 + X^22 + X^23 + X^24 + X^25 + X^26 + X^28
def r29_20 : P17 := 1 + X^2 + X^5 + X^10 + X^18 + X^24 + X^25 + X^27 + X^28
def r29_21 : P17 := X^2 + X^4 + X^7 + X^9 + X^10 + X^19 + X^20 + X^23 + X^25
def r29_22 : P17 := X^4 + X^8 + X^9 + X^13 + X^14 + X^17 + X^18 + X^19 + X^20 + X^21 + X^23
def r29_23 : P17 := X^5 + X^8 + X^15 + X^16 + X^17 + X^18 + X^19 + X^26 + X^28
def r29_24 : P17 := 1 + X^1 + X^2 + X^10 + X^11 + X^16 + X^23 + X^25 + X^27
def r29_25 : P17 := 1 + X^2 + X^3 + X^4 + X^5 + X^17 + X^19 + X^20 + X^21 + X^22 + X^23 + X^25 + X^27
def r29_26 : P17 := 1 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^19 + X^21 + X^23 + X^25 + X^27
def r29_27 : P17 := 1 + X^8 + X^9 + X^10 + X^11 + X^12 + X^13 + X^14 + X^15 + X^16 + X^17 + X^18 + X^19 + X^20 + X^21 + X^23 + X^25 + X^27
def r29_28 : P17 := 1 + X^1 + X^15 + X^16 + X^17 + X^18 + X^19 + X^20 + X^21 + X^22 + X^23 + X^24 + X^25 + X^26 + X^27 + X^28
def r29_29 : P17 := X^1
lemma f29_square_step {a r s q : P17} (h : f29 ∣ a+r) (hr : r^2+s=f29*q) : f29 ∣ a^2+s := by
  have h1 : f29 ∣ (a+r)^2 := dvd_pow h (by norm_num)
  have h2 : f29 ∣ r^2+s := ⟨q,hr⟩
  have h3 : f29 ∣ (a+r)^2+(r^2+s) := dvd_add h1 h2
  have heq : (a+r)^2+(r^2+s)=a^2+s := by ring_nf <;> simp [c2_17]
  rw [heq] at h3; exact h3
