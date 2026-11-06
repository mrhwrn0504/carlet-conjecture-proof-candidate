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
def f23 : P17 := X^23 + X^5 + 1
def r23_0 : P17 := X^1
def r23_1 : P17 := X^2
def r23_2 : P17 := X^4
def r23_3 : P17 := X^8
def r23_4 : P17 := X^16
def r23_5 : P17 := X^9 + X^14
def r23_6 : P17 := X^5 + X^10 + X^18
def r23_7 : P17 := X^10 + X^13 + X^18 + X^20
def r23_8 : P17 := X^3 + X^8 + X^13 + X^17 + X^18 + X^20 + X^22
def r23_9 : P17 := X^6 + X^11 + X^13 + X^17 + X^18 + X^21 + X^22
def r23_10 : P17 := X^1 + X^6 + X^11 + X^12 + X^13 + X^16 + X^18 + X^19 + X^21 + X^22
def r23_11 : P17 := X^2 + X^9 + X^12 + X^13 + X^14 + X^15 + X^18 + X^19 + X^20 + X^21 + X^22
def r23_12 : P17 := X^4 + X^5 + X^7 + X^10 + X^12 + X^13 + X^15 + X^17 + X^19 + X^20 + X^21 + X^22
def r23_13 : P17 := X^7 + X^8 + X^10 + X^11 + X^12 + X^14 + X^15 + X^16 + X^17 + X^19 + X^21 + X^22
def r23_14 : P17 := X^3 + X^5 + X^7 + X^8 + X^9 + X^10 + X^11 + X^12 + X^15 + X^19 + X^21 + X^22
def r23_15 : P17 := X^3 + X^6 + X^7 + X^8 + X^10 + X^12 + X^14 + X^15 + X^16 + X^18 + X^19 + X^21 + X^22
def r23_16 : P17 := X^3 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^13 + X^15 + X^16 + X^18 + X^19 + X^21
def r23_17 : P17 := X^1 + X^3 + X^7 + X^8 + X^9 + X^10 + X^13 + X^15 + X^16 + X^19
def r23_18 : P17 := X^2 + X^3 + X^6 + X^7 + X^8 + X^9 + X^12 + X^15 + X^16 + X^18
def r23_19 : P17 := X^1 + X^4 + X^7 + X^9 + X^13 + X^16
def r23_20 : P17 := X^2 + X^3 + X^9 + X^18
def r23_21 : P17 := X^4 + X^6 + X^13
def r23_22 : P17 := X^3 + X^12
def r23_23 : P17 := X^1

lemma f23_square_step {a r s q:P17} (h:f23∣a+r) (hr:r^2+s=f23*q) : f23∣a^2+s := by
  have h1:f23∣(a+r)^2 := dvd_pow h (by norm_num)
  have h2:f23∣r^2+s := ⟨q,hr⟩
  have h3:f23∣(a+r)^2+(r^2+s) := dvd_add h1 h2
  have heq:(a+r)^2+(r^2+s)=a^2+s := by ring_nf <;> simp [c2_17]
  rw [heq] at h3; exact h3

def frobExpAux : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * frobExpAux n

@[irreducible] def frobExp (n : Nat) : Nat := frobExpAux n

lemma frobExp_succ (n : Nat) : frobExp (n+1) = 2 * frobExp n := by
  unfold frobExp
  simp [frobExpAux]

lemma frobExp_zero : frobExp 0 = 1 := by
  unfold frobExp
  rfl

lemma frobExp_eq_pow (n : Nat) : frobExp n = 2^n := by
  induction n with
  | zero => simp [frobExp_zero]
  | succ n ih =>
      rw [frobExp_succ, ih, pow_succ]
      exact Nat.mul_comm _ _

def frobPolyAux (x : P17) : Nat → P17
  | 0 => x
  | n + 1 => (frobPolyAux x n)^2

@[irreducible] def frobPoly (n : Nat) : P17 := frobPolyAux X n

lemma frobPoly_zero : frobPoly 0 = X := by
  unfold frobPoly
  rfl

lemma frobPoly_succ (n : Nat) : frobPoly (n+1) = (frobPoly n)^2 := by
  unfold frobPoly
  simp [frobPolyAux]

lemma frobPoly_eq_pow (n : Nat) : frobPoly n = (X:P17)^(2^n:Nat) := by
  induction n with
  | zero => simp [frobPoly_zero]
  | succ n ih =>
      rw [frobPoly_succ, ih]
      rw [← pow_mul, pow_succ]

lemma f23_frob_step (m : Nat) {r s q : P17}
    (h : f23 ∣ frobPoly m + r) (hr : r^2+s=f23*q) :
    f23 ∣ frobPoly (m+1) + s := by
  have hs := f23_square_step h hr
  have hp : (frobPoly m)^2 = frobPoly (m+1) := (frobPoly_succ m).symm
  exact (congrArg (fun z:P17 => f23 ∣ z + s) hp).mp hs
