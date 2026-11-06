import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.defProp false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 32768
open Polynomial
noncomputable section
abbrev F13 := ZMod 2
abbrev P13 := Polynomial F13
lemma natCast_mod_two_13 (R : Type*) [Semiring R] [CharP R 2] (n : Nat) :
    (n : R) = ((n % 2 : Nat) : R) := by
  have hn : n = n % 2 + 2 * (n / 2) := (Nat.mod_add_div n 2).symm
  calc
    (n : R) = ((n % 2 + 2 * (n / 2) : Nat) : R) := congrArg (fun m : Nat => (m : R)) hn
    _ = ((n % 2 : Nat) : R) + ((2 * (n / 2) : Nat) : R) := by exact_mod_cast rfl
    _ = ((n % 2 : Nat) : R) := by rw [Nat.cast_mul, CharP.cast_eq_zero R 2]; simp
def f13 : P13 := X^13 + (X^4 + (X^3 + (X + 1)))
lemma c2_13 : (2:P13) = 0 := by
  change (( 2 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c3_13 : (3:P13) = 1 := by
  change (( 3 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c4_13 : (4:P13) = 0 := by
  change (( 4 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c5_13 : (5:P13) = 1 := by
  change (( 5 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c6_13 : (6:P13) = 0 := by
  change (( 6 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c7_13 : (7:P13) = 1 := by
  change (( 7 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c8_13 : (8:P13) = 0 := by
  change (( 8 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c9_13 : (9:P13) = 1 := by
  change (( 9 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c10_13 : (10:P13) = 0 := by
  change (( 10 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c11_13 : (11:P13) = 1 := by
  change (( 11 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c12_13 : (12:P13) = 0 := by
  change (( 12 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c13_13 : (13:P13) = 1 := by
  change (( 13 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c14_13 : (14:P13) = 0 := by
  change (( 14 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c15_13 : (15:P13) = 1 := by
  change (( 15 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c16_13 : (16:P13) = 0 := by
  change (( 16 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c17_13 : (17:P13) = 1 := by
  change (( 17 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c18_13 : (18:P13) = 0 := by
  change (( 18 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c19_13 : (19:P13) = 1 := by
  change (( 19 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c20_13 : (20:P13) = 0 := by
  change (( 20 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c21_13 : (21:P13) = 1 := by
  change (( 21 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c22_13 : (22:P13) = 0 := by
  change (( 22 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c23_13 : (23:P13) = 1 := by
  change (( 23 : Nat) : P13) = 1
  rw [natCast_mod_two_13]
  norm_num
lemma c24_13 : (24:P13) = 0 := by
  change (( 24 : Nat) : P13) = 0
  rw [natCast_mod_two_13]
  norm_num
lemma c5F13 : (5:F13) = 1 := by
  change ((5:Nat):F13) = 1
  rw [natCast_mod_two_13 F13 5]
  norm_num
def r0_13 : P13 := X^1
def r1_13 : P13 := X^2
def r2_13 : P13 := X^4
def r3_13 : P13 := X^8
def r4_13 : P13 := X^3 + X^4 + X^6 + X^7
def r5_13 : P13 := X^1 + X^2 + X^4 + X^5 + X^6 + X^8 + X^12
def r6_13 : P13 := X^1 + X^2 + X^4 + X^7 + X^8 + X^10 + X^11
def r7_13 : P13 := 1 + X^5 + X^6 + X^9 + X^11 + X^12
def r8_13 : P13 := X^5 + X^8 + X^11 + X^12
def r9_13 : P13 := 1 + X^3 + X^4 + X^7 + X^9 + X^11
def r10_13 : P13 := X^2 + X^3 + X^10 + X^12
def r11_13 : P13 := X^1 + X^3 + X^7 + X^8 + X^10 + X^12
def r12_13 : P13 := X^4 + X^5 + X^6 + X^8 + X^10 + X^12
def r13_13 : P13 := X^1
def q0_13 : P13 := 0
def q1_13 : P13 := 0
def q2_13 : P13 := 0
def q3_13 : P13 := X^3
def q4_13 : P13 := X^1
def q5_13 : P13 := X^1 + X^2 + X^3 + X^11
def q6_13 : P13 := 1 + X^1 + X^3 + X^7 + X^9
def q7_13 : P13 := 1 + X^1 + X^2 + X^5 + X^9 + X^11
def q8_13 : P13 := 1 + X^1 + X^2 + X^3 + X^9 + X^11
def q9_13 : P13 := 1 + X^1 + X^5 + X^9
def q10_13 : P13 := X^1 + X^2 + X^7 + X^11
def q11_13 : P13 := X^2 + X^3 + X^7 + X^11
def q12_13 : P13 := X^1 + X^2 + X^3 + X^7 + X^11
theorem rel0_13 : r0_13^2 + r1_13 = f13*q0_13 := by
  unfold r0_13 r1_13 f13 q0_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel1_13 : r1_13^2 + r2_13 = f13*q1_13 := by
  unfold r1_13 r2_13 f13 q1_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel2_13 : r2_13^2 + r3_13 = f13*q2_13 := by
  unfold r2_13 r3_13 f13 q2_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel3_13 : r3_13^2 + r4_13 = f13*q3_13 := by
  unfold r3_13 r4_13 f13 q3_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel4_13 : r4_13^2 + r5_13 = f13*q4_13 := by
  unfold r4_13 r5_13 f13 q4_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel5_13 : r5_13^2 + r6_13 = f13*q5_13 := by
  unfold r5_13 r6_13 f13 q5_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel6_13 : r6_13^2 + r7_13 = f13*q6_13 := by
  unfold r6_13 r7_13 f13 q6_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel7_13 : r7_13^2 + r8_13 = f13*q7_13 := by
  unfold r7_13 r8_13 f13 q7_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel8_13 : r8_13^2 + r9_13 = f13*q8_13 := by
  unfold r8_13 r9_13 f13 q8_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel9_13 : r9_13^2 + r10_13 = f13*q9_13 := by
  unfold r9_13 r10_13 f13 q9_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel10_13 : r10_13^2 + r11_13 = f13*q10_13 := by
  unfold r10_13 r11_13 f13 q10_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel11_13 : r11_13^2 + r12_13 = f13*q11_13 := by
  unfold r11_13 r12_13 f13 q11_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
theorem rel12_13 : r12_13^2 + r13_13 = f13*q12_13 := by
  unfold r12_13 r13_13 f13 q12_13
  ring_nf <;> simp [c2_13, c3_13, c4_13, c5_13, c6_13, c7_13, c8_13, c9_13, c10_13, c11_13, c12_13, c13_13, c14_13, c15_13, c16_13, c17_13, c18_13, c19_13, c20_13, c21_13, c22_13, c23_13, c24_13]
lemma square_step_13 {a r s q : P13} (h : f13 ∣ a + r) (hr : r^2 + s = f13*q) :
    f13 ∣ a^2 + s := by
  have h1 : f13 ∣ (a+r)^2 := dvd_pow h (by norm_num)
  have h2 : f13 ∣ r^2+s := ⟨q, hr⟩
  have h3 : f13 ∣ (a+r)^2 + (r^2+s) := dvd_add h1 h2
  have heq : (a+r)^2 + (r^2+s) = a^2+s := by ring_nf <;> simp [c2_13]
  rw [heq] at h3
  exact h3
lemma Xpow_square_13 (n : Nat) : ((X : P13)^(2^n))^2 = (X : P13)^(2^(n+1)) := by rw [← pow_mul, Nat.pow_succ]
theorem f13_dvd_frob_plus : f13 ∣ X^(2^13 : Nat) + X := by
  have h0 : f13 ∣ (X : P13)^(2^0 : Nat) + r0_13 := by
    have hx : (X : P13) + X = 0 := by
      have ht := congrArg (fun z : P13 => z * X) c2_13
      simpa [two_mul] using ht
    have he : (X : P13)^(2^0 : Nat) + r0_13 = 0 := by simpa [r0_13] using hx
    rw [he]
    exact dvd_zero f13
  have h1 : f13 ∣ (X : P13)^(2^1 : Nat) + r1_13 := by
    have h := square_step_13 h0 rel0_13
    simpa only [Xpow_square_13] using h
  have h2 : f13 ∣ (X : P13)^(2^2 : Nat) + r2_13 := by
    have h := square_step_13 h1 rel1_13
    simpa only [Xpow_square_13] using h
  have h3 : f13 ∣ (X : P13)^(2^3 : Nat) + r3_13 := by
    have h := square_step_13 h2 rel2_13
    simpa only [Xpow_square_13] using h
  have h4 : f13 ∣ (X : P13)^(2^4 : Nat) + r4_13 := by
    have h := square_step_13 h3 rel3_13
    simpa only [Xpow_square_13] using h
  have h5 : f13 ∣ (X : P13)^(2^5 : Nat) + r5_13 := by
    have h := square_step_13 h4 rel4_13
    simpa only [Xpow_square_13] using h
  have h6 : f13 ∣ (X : P13)^(2^6 : Nat) + r6_13 := by
    have h := square_step_13 h5 rel5_13
    simpa only [Xpow_square_13] using h
  have h7 : f13 ∣ (X : P13)^(2^7 : Nat) + r7_13 := by
    have h := square_step_13 h6 rel6_13
    simpa only [Xpow_square_13] using h
  have h8 : f13 ∣ (X : P13)^(2^8 : Nat) + r8_13 := by
    have h := square_step_13 h7 rel7_13
    simpa only [Xpow_square_13] using h
  have h9 : f13 ∣ (X : P13)^(2^9 : Nat) + r9_13 := by
    have h := square_step_13 h8 rel8_13
    simpa only [Xpow_square_13] using h
  have h10 : f13 ∣ (X : P13)^(2^10 : Nat) + r10_13 := by
    have h := square_step_13 h9 rel9_13
    simpa only [Xpow_square_13] using h
  have h11 : f13 ∣ (X : P13)^(2^11 : Nat) + r11_13 := by
    have h := square_step_13 h10 rel10_13
    simpa only [Xpow_square_13] using h
  have h12 : f13 ∣ (X : P13)^(2^12 : Nat) + r12_13 := by
    have h := square_step_13 h11 rel11_13
    simpa only [Xpow_square_13] using h
  have h13 : f13 ∣ (X : P13)^(2^13 : Nat) + r13_13 := by
    have h := square_step_13 h12 rel12_13
    simpa only [Xpow_square_13] using h
  simpa [r13_13] using h13
#print axioms f13_dvd_frob_plus

theorem f13_dvd_frob_sub : f13 ∣ (X : P13)^(2^13 : Nat) - X := by
  have h := f13_dvd_frob_plus
  have hneg : -(X : P13) = X := by
    have hx : (X : P13) + X = 0 := by
      have hx' := congrArg (fun z : P13 => z * X) c2_13
      simpa [two_mul] using hx'
    exact neg_eq_of_add_eq_zero_left hx
  convert h using 1 <;> simp [sub_eq_add_neg, hneg]

lemma f13_no_roots (x : F13) : eval x f13 ≠ 0 := by
  have hv : x.val = 0 ∨ x.val = 1 := by
    have hx := ZMod.val_lt x
    omega
  rcases hv with hv | hv
  · have hx : x = 0 := by
      apply ZMod.val_injective 2
      simpa [hv]
    subst x
    simp [f13, eval_add, eval_pow, eval_X, eval_one]
  · have hx : x = 1 := by
      apply ZMod.val_injective 2
      rw [hv]
      exact ZMod.val_cast_of_lt (by norm_num : (1:Nat) < 2)
    subst x
    simp only [f13, eval_add, eval_pow, eval_X, eval_one]
    norm_num [c2_13]
    rw [c5F13]
    norm_num

lemma f13_irreducible : Irreducible f13 := by
  have hfmonic : f13.Monic := by unfold f13; monicity <;> norm_num
  have hfdeg : f13.natDegree = 13 := by
    change (X^13 + (X^4 + (X^3 + (X + 1)) : P13)).natDegree = 13
    have h1 : ((X : P13) + 1).natDegree ≤ 1 := by
      calc
        _ ≤ max (X : P13).natDegree (1 : P13).natDegree := Polynomial.natDegree_add_le _ _
        _ = 1 := by simp
    have h3 : ((X : P13)^3 + (X + 1)).natDegree ≤ 3 := by
      calc
        _ ≤ max ((X : P13)^3).natDegree (X + 1).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 3 := by simp only [Polynomial.natDegree_X_pow]; omega
    have h4 : ((X : P13)^4 + (X^3 + (X + 1))).natDegree ≤ 4 := by
      calc
        _ ≤ max ((X : P13)^4).natDegree (X^3 + (X + 1)).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 4 := by simp only [Polynomial.natDegree_X_pow]; omega
    have hs : ((X : P13)^4 + (X^3 + (X + 1))).natDegree < 13 := by omega
    have hp : ((X : P13)^13).natDegree = 13 := Polynomial.natDegree_X_pow 13
    have hs' : ((X : P13)^4 + (X^3 + (X + 1))).natDegree < ((X : P13)^13).natDegree := by
      rw [hp]
      exact hs
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
    exact hp
  have hf0 : f13 ≠ 0 := by intro hz; rw [hz] at hfdeg; norm_num at hfdeg
  have hfne : f13 ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    rw [hfdeg] at hd
    norm_num at hd
  rw [Polynomial.Monic.irreducible_iff_degree_lt hfmonic hfne]
  intro q hqdeg hqf
  by_contra hqnot
  obtain ⟨g, hgmon, hgirr, hgq⟩ := Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hqf
    exact hf0 hqf
  have hqNat : q.natDegree ≤ 6 := by
    rw [Polynomial.degree_eq_natDegree hq0] at hqdeg
    rw [hfdeg] at hqdeg
    norm_num at hqdeg
    exact_mod_cast hqdeg
  have hgNat : g.natDegree ≤ q.natDegree := Polynomial.natDegree_le_of_dvd hgq hq0
  have hgBound : g.natDegree ≤ 6 := hgNat.trans hqNat
  have hgfrob : g ∣ (X : P13) ^ (Nat.card F13) ^ 13 - X := by
    have hgF : g ∣ f13 := dvd_trans hgq hqf
    have := dvd_trans hgF f13_dvd_frob_sub
    simpa [Nat.card_eq_fintype_card, ZMod.card] using this
  have hdiv : g.natDegree ∣ 13 :=
    (hgirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 13)).2 hgfrob
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hdiv with hone | h13
  · have hgdeg1 : g.natDegree = 1 := hone
    rcases (Polynomial.natDegree_eq_one).mp hgdeg1 with ⟨a, ha, b, hrepr⟩
    let root : F13 := -b / a
    have hroot : g.IsRoot root := by
      change eval root g = 0
      rw [← hrepr, eval_add, eval_mul, eval_C, eval_X, eval_C]
      dsimp [root]
      field_simp [ha] <;> ring_nf <;> simp [c2_13]
    have hfroot : f13.IsRoot root := hroot.dvd (dvd_trans hgq hqf)
    exact f13_no_roots root hfroot
  · omega

#print axioms f13_irreducible
