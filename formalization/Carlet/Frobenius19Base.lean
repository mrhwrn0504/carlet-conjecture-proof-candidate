import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
abbrev F19 := ZMod 2
abbrev P19 := Polynomial F19
def f19 : P19 := X^19 + (X^5 + (X^2 + (X + 1)))
lemma natCast_mod_two_19 (R : Type*) [Semiring R] [CharP R 2] (n : Nat) : (n : R) = ((n % 2 : Nat) : R) := by
  have hn : n = n % 2 + 2 * (n / 2) := (Nat.mod_add_div n 2).symm
  calc
    (n : R) = ((n % 2 + 2 * (n / 2) : Nat) : R) := congrArg (fun m : Nat => (m : R)) hn
    _ = ((n % 2 : Nat) : R) + ((2 * (n / 2) : Nat) : R) := by exact_mod_cast rfl
    _ = ((n % 2 : Nat) : R) := by rw [Nat.cast_mul, CharP.cast_eq_zero R 2]; simp
lemma c2_19 : (2:P19) = 0 := by
  change ((2:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c3_19 : (3:P19) = 1 := by
  change ((3:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c4_19 : (4:P19) = 0 := by
  change ((4:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c5_19 : (5:P19) = 1 := by
  change ((5:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c6_19 : (6:P19) = 0 := by
  change ((6:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c7_19 : (7:P19) = 1 := by
  change ((7:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c8_19 : (8:P19) = 0 := by
  change ((8:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c9_19 : (9:P19) = 1 := by
  change ((9:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c10_19 : (10:P19) = 0 := by
  change ((10:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c11_19 : (11:P19) = 1 := by
  change ((11:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c12_19 : (12:P19) = 0 := by
  change ((12:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c13_19 : (13:P19) = 1 := by
  change ((13:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c14_19 : (14:P19) = 0 := by
  change ((14:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c15_19 : (15:P19) = 1 := by
  change ((15:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c16_19 : (16:P19) = 0 := by
  change ((16:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c17_19 : (17:P19) = 1 := by
  change ((17:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c18_19 : (18:P19) = 0 := by
  change ((18:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c19_19 : (19:P19) = 1 := by
  change ((19:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c20_19 : (20:P19) = 0 := by
  change ((20:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c21_19 : (21:P19) = 1 := by
  change ((21:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c22_19 : (22:P19) = 0 := by
  change ((22:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c23_19 : (23:P19) = 1 := by
  change ((23:Nat):P19) = 1
  rw [natCast_mod_two_19]
  norm_num
lemma c24_19 : (24:P19) = 0 := by
  change ((24:Nat):P19) = 0
  rw [natCast_mod_two_19]
  norm_num
lemma c2_F19 : (2:F19) = 0 := by
  change ((2:Nat):F19) = 0
  rw [natCast_mod_two_19]
  norm_num
def r0_19 : P19 := X^1
def r1_19 : P19 := X^2
def r2_19 : P19 := X^4
def r3_19 : P19 := X^8
def r4_19 : P19 := X^16
def r5_19 : P19 := X^13 + X^14 + X^15 + X^18
def r6_19 : P19 := 1 + X^1 + X^2 + X^3 + X^4 + X^7 + X^10 + X^13 + X^14 + X^16 + X^17 + X^18
def r7_19 : P19 := X^1 + X^3 + X^6 + X^7 + X^8 + X^10 + X^11 + X^12 + X^13 + X^14 + X^16
def r8_19 : P19 := X^1 + X^4 + X^6 + X^11 + X^13 + X^14 + X^15 + X^16 + X^18
def r9_19 : P19 := 1 + X^1 + X^5 + X^7 + X^10 + X^12 + X^15 + X^16 + X^17
def r10_19 : P19 := 1 + X^2 + X^5 + X^6 + X^7 + X^11 + X^12 + X^17 + X^18
def r11_19 : P19 := X^3 + X^4 + X^7 + X^12 + X^14 + X^15 + X^16 + X^18
def r12_19 : P19 := 1 + X^1 + X^2 + X^3 + X^4 + X^5 + X^7 + X^9 + X^12 + X^14 + X^15 + X^16 + X^17
def r13_19 : P19 := 1 + X^1 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^12 + X^14 + X^17
def r14_19 : P19 := 1 + X^2 + X^5 + X^7 + X^8 + X^9 + X^10 + X^11 + X^12 + X^15 + X^17 + X^18
def r15_19 : P19 := X^1 + X^2 + X^4 + X^6 + X^7 + X^11 + X^12 + X^13 + X^14 + X^15 + X^16
def r16_19 : P19 := X^2 + X^3 + X^6 + X^8 + X^12 + X^14 + X^15 + X^16 + X^18
def r17_19 : P19 := 1 + X^1 + X^2 + X^3 + X^5 + X^7 + X^8 + X^9 + X^15 + X^17
def r18_19 : P19 := 1 + X^1 + X^3 + X^4 + X^10 + X^11 + X^12 + X^13 + X^14 + X^15 + X^16 + X^17 + X^18
def r19_19 : P19 := X^1
def q0_19 : P19 := 0
def q1_19 : P19 := 0
def q2_19 : P19 := 0
def q3_19 : P19 := 0
def q4_19 : P19 := X^13
def q5_19 : P19 := 1 + X^3 + X^7 + X^9 + X^11 + X^17
def q6_19 : P19 := 1 + X^3 + X^7 + X^9 + X^13 + X^15 + X^17
def q7_19 : P19 := X^1 + X^3 + X^5 + X^7 + X^9 + X^13
def q8_19 : P19 := 1 + X^7 + X^9 + X^11 + X^13 + X^17
def q9_19 : P19 := X^5 + X^11 + X^13 + X^15
def q10_19 : P19 := 1 + X^1 + X^5 + X^15 + X^17
def q11_19 : P19 := 1 + X^3 + X^5 + X^9 + X^11 + X^13 + X^17
def q12_19 : P19 := X^1 + X^5 + X^9 + X^11 + X^13 + X^15
def q13_19 : P19 := X^5 + X^9 + X^15
def q14_19 : P19 := 1 + X^5 + X^11 + X^15 + X^17
def q15_19 : P19 := X^3 + X^5 + X^7 + X^9 + X^11 + X^13
def q16_19 : P19 := 1 + X^3 + X^5 + X^9 + X^11 + X^13 + X^17
def q17_19 : P19 := X^1 + X^11 + X^15
def q18_19 : P19 := 1 + X^5 + X^7 + X^9 + X^11 + X^13 + X^15 + X^17
theorem rel0_19 : r0_19^2 + r1_19 = f19*q0_19 := by
  unfold r0_19 r1_19 f19 q0_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
theorem rel1_19 : r1_19^2 + r2_19 = f19*q1_19 := by
  unfold r1_19 r2_19 f19 q1_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
theorem rel2_19 : r2_19^2 + r3_19 = f19*q2_19 := by
  unfold r2_19 r3_19 f19 q2_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
theorem rel3_19 : r3_19^2 + r4_19 = f19*q3_19 := by
  unfold r3_19 r4_19 f19 q3_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
theorem rel4_19 : r4_19^2 + r5_19 = f19*q4_19 := by
  unfold r4_19 r5_19 f19 q4_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
theorem rel5_19 : r5_19^2 + r6_19 = f19*q5_19 := by
  unfold r5_19 r6_19 f19 q5_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
theorem rel6_19 : r6_19^2 + r7_19 = f19*q6_19 := by
  unfold r6_19 r7_19 f19 q6_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
