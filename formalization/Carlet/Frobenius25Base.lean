import Carlet.Frobenius17Probe
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def f25 : P17 := X^25 + X^3 + 1
def r25_0 : P17 := X^1
def r25_1 : P17 := X^2
def r25_2 : P17 := X^4
def r25_3 : P17 := X^8
def r25_4 : P17 := X^16
def r25_5 : P17 := X^7 + X^10
def r25_6 : P17 := X^14 + X^20
def r25_7 : P17 := X^3 + X^6 + X^15 + X^18
def r25_8 : P17 := X^5 + X^6 + X^8 + X^11 + X^12 + X^14
def r25_9 : P17 := X^3 + X^6 + X^10 + X^12 + X^16 + X^22 + X^24
def r25_10 : P17 := X^1 + X^4 + X^6 + X^7 + X^10 + X^12 + X^19 + X^20 + X^22 + X^23 + X^24
def r25_11 : P17 := X^1 + X^2 + X^4 + X^8 + X^12 + X^13 + X^14 + X^15 + X^16 + X^18 + X^19 + X^20 + X^21 + X^22 + X^23
def r25_12 : P17 := X^1 + X^2 + X^3 + X^5 + X^6 + X^7 + X^10 + X^11 + X^13 + X^14 + X^15 + X^17 + X^18 + X^19 + X^20 + X^21 + X^22
def r25_13 : P17 := X^1 + X^2 + X^3 + X^5 + X^8 + X^9 + X^10 + X^11 + X^13 + X^15 + X^16 + X^17 + X^18 + X^19
def r25_14 : P17 := X^1 + X^2 + X^5 + X^6 + X^7 + X^8 + X^9 + X^11 + X^12 + X^13 + X^14 + X^18 + X^20 + X^22
def r25_15 : P17 := X^1 + X^2 + X^3 + X^6 + X^10 + X^11 + X^12 + X^15 + X^16 + X^19 + X^24
def r25_16 : P17 := X^1 + X^2 + X^5 + X^6 + X^7 + X^8 + X^10 + X^12 + X^13 + X^16 + X^20 + X^22 + X^23 + X^24
def r25_17 : P17 := X^2 + X^4 + X^7 + X^12 + X^14 + X^15 + X^16 + X^18 + X^19 + X^20 + X^21 + X^22 + X^23
def r25_18 : P17 := X^3 + X^4 + X^5 + X^6 + X^7 + X^10 + X^11 + X^13 + X^15 + X^16 + X^17 + X^18 + X^19 + X^20 + X^21 + X^22
def r25_19 : P17 := X^1 + X^4 + X^5 + X^6 + X^7 + X^9 + X^11 + X^13 + X^15 + X^16 + X^17 + X^18 + X^19
def r25_20 : P17 := X^1 + X^2 + X^4 + X^5 + X^7 + X^9 + X^11 + X^13 + X^16 + X^18 + X^22
def r25_21 : P17 := X^1 + X^2 + X^7 + X^8 + X^11 + X^18 + X^19
def r25_22 : P17 := X^2 + X^4 + X^11 + X^13 + X^22
def r25_23 : P17 := X^1 + X^8 + X^19
def r25_24 : P17 := X^2 + X^13
def r25_25 : P17 := X^1

lemma f25_square_step {a r s q:P17} (h:f25∣a+r) (hr:r^2+s=f25*q) : f25∣a^2+s := by
  have h1:f25∣(a+r)^2 := dvd_pow h (by norm_num)
  have h2:f25∣r^2+s := ⟨q,hr⟩
  have h3:f25∣(a+r)^2+(r^2+s) := dvd_add h1 h2
  have heq:(a+r)^2+(r^2+s)=a^2+s := by ring_nf <;> simp [c2_17]
  rw [heq] at h3; exact h3
