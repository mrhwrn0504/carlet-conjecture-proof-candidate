import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
abbrev F17 := ZMod 2
abbrev P17 := Polynomial F17
lemma natCast_mod_two_17 (R : Type*) [Semiring R] [CharP R 2] (n : Nat) : (n : R) = ((n % 2 : Nat) : R) := by
  have hn : n = n % 2 + 2 * (n / 2) := (Nat.mod_add_div n 2).symm
  calc
    (n : R) = ((n % 2 + 2 * (n / 2) : Nat) : R) := congrArg (fun m : Nat => (m : R)) hn
    _ = ((n % 2 : Nat) : R) + ((2 * (n / 2) : Nat) : R) := by exact_mod_cast rfl
    _ = ((n % 2 : Nat) : R) := by rw [Nat.cast_mul, CharP.cast_eq_zero R 2]; simp
def f17 : P17 := X^17 + (X^3 + 1)
lemma c2_17 : (2:P17) = 0 := by
  change ((2:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c3_17 : (3:P17) = 1 := by
  change ((3:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c4_17 : (4:P17) = 0 := by
  change ((4:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c5_17 : (5:P17) = 1 := by
  change ((5:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c6_17 : (6:P17) = 0 := by
  change ((6:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c7_17 : (7:P17) = 1 := by
  change ((7:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c8_17 : (8:P17) = 0 := by
  change ((8:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c9_17 : (9:P17) = 1 := by
  change ((9:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c10_17 : (10:P17) = 0 := by
  change ((10:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c11_17 : (11:P17) = 1 := by
  change ((11:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c12_17 : (12:P17) = 0 := by
  change ((12:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c13_17 : (13:P17) = 1 := by
  change ((13:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c14_17 : (14:P17) = 0 := by
  change ((14:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c15_17 : (15:P17) = 1 := by
  change ((15:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c16_17 : (16:P17) = 0 := by
  change ((16:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c17_17 : (17:P17) = 1 := by
  change ((17:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c18_17 : (18:P17) = 0 := by
  change ((18:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c19_17 : (19:P17) = 1 := by
  change ((19:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c20_17 : (20:P17) = 0 := by
  change ((20:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c21_17 : (21:P17) = 1 := by
  change ((21:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c22_17 : (22:P17) = 0 := by
  change ((22:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c23_17 : (23:P17) = 1 := by
  change ((23:Nat):P17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c24_17 : (24:P17) = 0 := by
  change ((24:Nat):P17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c2_F17 : (2:F17) = 0 := by
  change ((2:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c3_F17 : (3:F17) = 1 := by
  change ((3:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c4_F17 : (4:F17) = 0 := by
  change ((4:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c5_F17 : (5:F17) = 1 := by
  change ((5:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c6_F17 : (6:F17) = 0 := by
  change ((6:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c7_F17 : (7:F17) = 1 := by
  change ((7:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c8_F17 : (8:F17) = 0 := by
  change ((8:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c9_F17 : (9:F17) = 1 := by
  change ((9:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c10_F17 : (10:F17) = 0 := by
  change ((10:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c11_F17 : (11:F17) = 1 := by
  change ((11:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c12_F17 : (12:F17) = 0 := by
  change ((12:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c13_F17 : (13:F17) = 1 := by
  change ((13:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c14_F17 : (14:F17) = 0 := by
  change ((14:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c15_F17 : (15:F17) = 1 := by
  change ((15:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c16_F17 : (16:F17) = 0 := by
  change ((16:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c17_F17 : (17:F17) = 1 := by
  change ((17:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c18_F17 : (18:F17) = 0 := by
  change ((18:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c19_F17 : (19:F17) = 1 := by
  change ((19:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c20_F17 : (20:F17) = 0 := by
  change ((20:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c21_F17 : (21:F17) = 1 := by
  change ((21:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c22_F17 : (22:F17) = 0 := by
  change ((22:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
lemma c23_F17 : (23:F17) = 1 := by
  change ((23:Nat):F17) = 1
  rw [natCast_mod_two_17]
  norm_num
lemma c24_F17 : (24:F17) = 0 := by
  change ((24:Nat):F17) = 0
  rw [natCast_mod_two_17]
  norm_num
def r0_17 : P17 := X^1
def r1_17 : P17 := X^2
def r2_17 : P17 := X^4
def r3_17 : P17 := X^8
def r4_17 : P17 := X^16
def r5_17 : P17 := X^1 + X^4 + X^15
def r6_17 : P17 := X^2 + X^8 + X^13 + X^16
def r7_17 : P17 := X^1 + X^9 + X^12 + X^15 + X^16
def r8_17 : P17 := X^2 + X^7 + X^10 + X^13 + X^15 + X^16
def r9_17 : P17 := X^1 + X^3 + X^6 + X^9 + X^12 + X^13 + X^14 + X^15 + X^16
def r10_17 : P17 := X^2 + X^6 + X^7 + X^9 + X^10 + X^11 + X^13 + X^14 + X^15 + X^16
def r11_17 : P17 := X^3 + X^4 + X^5 + X^6 + X^8 + X^9 + X^11 + X^13 + X^15 + X^16
def r12_17 : P17 := X^5 + X^6 + X^9 + X^10 + X^13 + X^15
def r13_17 : P17 := X^1 + X^3 + X^4 + X^6 + X^9 + X^10 + X^13 + X^16
def r14_17 : P17 := X^2 + X^3 + X^8 + X^9 + X^15
def r15_17 : P17 := X^1 + X^6 + X^13
def r16_17 : P17 := X^2 + X^9
def r17_17 : P17 := X^1
def q0_17 : P17 := 0
def q1_17 : P17 := 0
def q2_17 : P17 := 0
def q3_17 : P17 := 0
def q4_17 : P17 := X^1 + X^15
def q5_17 : P17 := X^13
def q6_17 : P17 := X^1 + X^9 + X^15
def q7_17 : P17 := X^7 + X^13 + X^15
def q8_17 : P17 := X^1 + X^3 + X^9 + X^13 + X^15
def q9_17 : P17 := X^7 + X^9 + X^11 + X^13 + X^15
def q10_17 : P17 := X^3 + X^5 + X^9 + X^11 + X^13 + X^15
def q11_17 : P17 := X^5 + X^9 + X^13 + X^15
def q12_17 : P17 := X^1 + X^3 + X^9 + X^13
def q13_17 : P17 := X^3 + X^9 + X^15
def q14_17 : P17 := X^1 + X^13
def q15_17 : P17 := X^9
def q16_17 : P17 := X^1
theorem rel0_17 : r0_17^2 + r1_17 = f17*q0_17 := by
  unfold r0_17 r1_17 f17 q0_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel1_17 : r1_17^2 + r2_17 = f17*q1_17 := by
  unfold r1_17 r2_17 f17 q1_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel2_17 : r2_17^2 + r3_17 = f17*q2_17 := by
  unfold r2_17 r3_17 f17 q2_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel3_17 : r3_17^2 + r4_17 = f17*q3_17 := by
  unfold r3_17 r4_17 f17 q3_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel4_17 : r4_17^2 + r5_17 = f17*q4_17 := by
  unfold r4_17 r5_17 f17 q4_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel5_17 : r5_17^2 + r6_17 = f17*q5_17 := by
  unfold r5_17 r6_17 f17 q5_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel6_17 : r6_17^2 + r7_17 = f17*q6_17 := by
  unfold r6_17 r7_17 f17 q6_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel7_17 : r7_17^2 + r8_17 = f17*q7_17 := by
  unfold r7_17 r8_17 f17 q7_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel8_17 : r8_17^2 + r9_17 = f17*q8_17 := by
  unfold r8_17 r9_17 f17 q8_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel9_17 : r9_17^2 + r10_17 = f17*q9_17 := by
  unfold r9_17 r10_17 f17 q9_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel10_17 : r10_17^2 + r11_17 = f17*q10_17 := by
  unfold r10_17 r11_17 f17 q10_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel11_17 : r11_17^2 + r12_17 = f17*q11_17 := by
  unfold r11_17 r12_17 f17 q11_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel12_17 : r12_17^2 + r13_17 = f17*q12_17 := by
  unfold r12_17 r13_17 f17 q12_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel13_17 : r13_17^2 + r14_17 = f17*q13_17 := by
  unfold r13_17 r14_17 f17 q13_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel14_17 : r14_17^2 + r15_17 = f17*q14_17 := by
  unfold r14_17 r15_17 f17 q14_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel15_17 : r15_17^2 + r16_17 = f17*q15_17 := by
  unfold r15_17 r16_17 f17 q15_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem rel16_17 : r16_17^2 + r17_17 = f17*q16_17 := by
  unfold r16_17 r17_17 f17 q16_17
  ring_nf
  simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma square_step_17 {a r s q : P17} (h : f17 ∣ a + r) (hr : r^2 + s = f17*q) : f17 ∣ a^2 + s := by
  have h1 : f17 ∣ (a+r)^2 := dvd_pow h (by norm_num)
  have h2 : f17 ∣ r^2+s := ⟨q,hr⟩
  have h3 : f17 ∣ (a+r)^2+(r^2+s) := dvd_add h1 h2
  have heq : (a+r)^2+(r^2+s)=a^2+s := by ring_nf <;> simp [c2_17]
  rw [heq] at h3
  exact h3
lemma Xpow_square_17 (m:Nat) : ((X:P17)^(2^m))^2=(X:P17)^(2^(m+1)) := by rw [← pow_mul,Nat.pow_succ]
theorem f17_dvd_frob_plus : f17 ∣ (X:P17)^(2^17:Nat)+X := by
  have h0 : f17 ∣ (X:P17)^(2^0:Nat)+r0_17 := by
    have hx : (X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
    have he : (X:P17)^(2^0:Nat)+r0_17=0 := by simpa [r0_17] using hx
    rw [he]; exact dvd_zero f17
  have h1 : f17 ∣ (X:P17)^(2^1:Nat)+r1_17 := by
    have h:=square_step_17 h0 rel0_17
    simpa only [Xpow_square_17] using h
  have h2 : f17 ∣ (X:P17)^(2^2:Nat)+r2_17 := by
    have h:=square_step_17 h1 rel1_17
    simpa only [Xpow_square_17] using h
  have h3 : f17 ∣ (X:P17)^(2^3:Nat)+r3_17 := by
    have h:=square_step_17 h2 rel2_17
    simpa only [Xpow_square_17] using h
  have h4 : f17 ∣ (X:P17)^(2^4:Nat)+r4_17 := by
    have h:=square_step_17 h3 rel3_17
    simpa only [Xpow_square_17] using h
  have h5 : f17 ∣ (X:P17)^(2^5:Nat)+r5_17 := by
    have h:=square_step_17 h4 rel4_17
    simpa only [Xpow_square_17] using h
  have h6 : f17 ∣ (X:P17)^(2^6:Nat)+r6_17 := by
    have h:=square_step_17 h5 rel5_17
    simpa only [Xpow_square_17] using h
  have h7 : f17 ∣ (X:P17)^(2^7:Nat)+r7_17 := by
    have h:=square_step_17 h6 rel6_17
    simpa only [Xpow_square_17] using h
  have h8 : f17 ∣ (X:P17)^(2^8:Nat)+r8_17 := by
    have h:=square_step_17 h7 rel7_17
    simpa only [Xpow_square_17] using h
  have h9 : f17 ∣ (X:P17)^(2^9:Nat)+r9_17 := by
    have h:=square_step_17 h8 rel8_17
    simpa only [Xpow_square_17] using h
  have h10 : f17 ∣ (X:P17)^(2^10:Nat)+r10_17 := by
    have h:=square_step_17 h9 rel9_17
    simpa only [Xpow_square_17] using h
  have h11 : f17 ∣ (X:P17)^(2^11:Nat)+r11_17 := by
    have h:=square_step_17 h10 rel10_17
    simpa only [Xpow_square_17] using h
  have h12 : f17 ∣ (X:P17)^(2^12:Nat)+r12_17 := by
    have h:=square_step_17 h11 rel11_17
    simpa only [Xpow_square_17] using h
  have h13 : f17 ∣ (X:P17)^(2^13:Nat)+r13_17 := by
    have h:=square_step_17 h12 rel12_17
    simpa only [Xpow_square_17] using h
  have h14 : f17 ∣ (X:P17)^(2^14:Nat)+r14_17 := by
    have h:=square_step_17 h13 rel13_17
    simpa only [Xpow_square_17] using h
  have h15 : f17 ∣ (X:P17)^(2^15:Nat)+r15_17 := by
    have h:=square_step_17 h14 rel14_17
    simpa only [Xpow_square_17] using h
  have h16 : f17 ∣ (X:P17)^(2^16:Nat)+r16_17 := by
    have h:=square_step_17 h15 rel15_17
    simpa only [Xpow_square_17] using h
  have h17 : f17 ∣ (X:P17)^(2^17:Nat)+r17_17 := by
    have h:=square_step_17 h16 rel16_17
    simpa only [Xpow_square_17] using h
  simpa [r17_17] using h17
theorem f17_dvd_frob_sub : f17 ∣ (X:P17)^(2^17:Nat)-X := by
  have h:=f17_dvd_frob_plus
  have hneg : -(X:P17)=X := by
    have hx:(X:P17)+X=0 := by
      have ht:=congrArg (fun z:P17=>z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  convert h using 1 <;> simp [sub_eq_add_neg,hneg]
lemma f17_no_roots (x:F17) : eval x f17 ≠ 0 := by
  have hv : x.val=0 ∨ x.val=1 := by have hx:=ZMod.val_lt x; omega
  rcases hv with hv|hv
  · have hx:x=0 := by apply ZMod.val_injective 2; simpa [hv]
    subst x; simp [f17]
  · have hx:x=1 := by apply ZMod.val_injective 2; rw [hv]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat)<2)
    subst x
    simp only [f17, eval_add, eval_pow, eval_X, eval_one]
    have h11 : (1:F17) + 1 = 0 := by
      calc
        (1:F17) + 1 = (2:F17) := by norm_num [two_mul]
        _ = 0 := c2_F17
    simp only [f17, eval_add, eval_pow, eval_X, eval_one, one_pow]
    rw [h11]
    simp
lemma f17_irreducible : Irreducible f17 := by
  have hm : f17.Monic := by unfold f17; monicity <;> norm_num
  have hd : f17.natDegree=17 := by
    have hs : ((X:P17)^3+1).natDegree ≤ 3 := by
      calc
        _ ≤ max ((X:P17)^3).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
        _ = 3 := by simp
    have hp : ((X:P17)^17).natDegree=17 := Polynomial.natDegree_X_pow 17
    have hs' : ((X:P17)^3+1).natDegree < ((X:P17)^17).natDegree := by rw [hp]; omega
    unfold f17; rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']; exact hp
  have h0 : f17 ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
  have hne : f17 ≠ 1 := by intro h; have hh:=congrArg Polynomial.natDegree h; rw [hd] at hh; norm_num at hh
  rw [Polynomial.Monic.irreducible_iff_degree_lt hm hne]
  intro q hqdeg hqf; by_contra hqnot
  obtain ⟨g,hgm,hgi,hgq⟩:=Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0:q≠0 := by intro h; subst q; simp at hqf; exact h0 hqf
  have hqN:q.natDegree≤8 := by rw [Polynomial.degree_eq_natDegree hq0] at hqdeg; rw [hd] at hqdeg; norm_num at hqdeg; exact_mod_cast hqdeg
  have hgN:g.natDegree≤q.natDegree := Polynomial.natDegree_le_of_dvd hgq hq0
  have hgB:g.natDegree≤8 := hgN.trans hqN
  have hgf:g ∣ (X:P17)^(Nat.card F17)^17-X := by have hf:g∣f17:=dvd_trans hgq hqf; have hh:=dvd_trans hf f17_dvd_frob_sub; simpa [Nat.card_eq_fintype_card,ZMod.card] using hh
  have hdiv:g.natDegree∣17 := (hgi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n:=17)).2 hgf
  rcases (Nat.dvd_prime (by norm_num:Nat.Prime 17)).mp hdiv with hone|h17
  · have hgd:g.natDegree=1:=hone
    rcases (Polynomial.natDegree_eq_one).mp hgd with ⟨a,ha,b,hrepr⟩
    let root:F17 := -b/a
    have hr : g.IsRoot root := by change eval root g=0; rw [← hrepr,eval_add,eval_mul,eval_C,eval_X,eval_C]; dsimp [root]; field_simp [ha] <;> ring_nf <;> simp
    exact f17_no_roots root (hr.dvd (dvd_trans hgq hqf))
  · omega
#print axioms f17_irreducible
