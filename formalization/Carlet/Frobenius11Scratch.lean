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
abbrev F := ZMod 2
abbrev P := Polynomial F
lemma natCast_mod_two (R : Type*) [Semiring R] [CharP R 2] (n : Nat) :
    (n : R) = ((n % 2 : Nat) : R) := by
  have hn : n = n % 2 + 2 * (n / 2) := (Nat.mod_add_div n 2).symm
  calc
    (n : R) = ((n % 2 + 2 * (n / 2) : Nat) : R) := congrArg (fun m : Nat => (m : R)) hn
    _ = ((n % 2 : Nat) : R) + ((2 * (n / 2) : Nat) : R) := by exact_mod_cast rfl
    _ = ((n % 2 : Nat) : R) := by rw [Nat.cast_mul, CharP.cast_eq_zero R 2]; simp
lemma c2 : (2:P)=0 := by change ((2:Nat):P)=0; rw [natCast_mod_two]; norm_num
lemma c3 : (3:P)=1 := by change ((3:Nat):P)=1; rw [natCast_mod_two]; norm_num
lemma c4 : (4:P)=0 := by change ((4:Nat):P)=0; rw [natCast_mod_two]; norm_num
lemma c5 : (5:P)=1 := by change ((5:Nat):P)=1; rw [natCast_mod_two]; norm_num
lemma c6 : (6:P)=0 := by change ((6:Nat):P)=0; rw [natCast_mod_two]; norm_num
lemma c7 : (7:P)=1 := by change ((7:Nat):P)=1; rw [natCast_mod_two]; norm_num
lemma c8 : (8:P)=0 := by change ((8:Nat):P)=0; rw [natCast_mod_two]; norm_num
def f : P := X^11 + X^2 + 1
def r0 : P := X
def r1 : P := X^2
def r2 : P := X^4
def r3 : P := X^8
def r4 : P := X^7 + X^5
def r5 : P := X^10 + X^5 + X^3
def r6 : P := X^10 + X^9 + X^6 + X^2 + 1
def r7 : P := X^7 + X^4 + X^3 + X^2 + X
def r8 : P := X^8 + X^6 + X^5 + X^4 + X^3 + X^2
def r9 : P := X^10 + X^8 + X^7 + X^6 + X^5 + X^4 + X^3 + X
def r10 : P := X^10 + X^9 + X^8 + X^7 + X^6 + X + 1
def r11 : P := X
def q0 : P := 0
def q1 : P := 0
def q2 : P := 0
def q3 : P := X^5
def q4 : P := X^3
def q5 : P := X^9 + 1
def q6 : P := X^9 + X^7 + X + 1
def q7 : P := X^3
def q8 : P := X^5 + X
def q9 : P := X^9 + X^5 + X^3 + X + 1
def q10 : P := X^9 + X^7 + X^5 + X^3 + X + 1
theorem rel0 : r0^2 + r1 = f*q0 := by unfold r0 r1 f q0; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel1 : r1^2 + r2 = f*q1 := by unfold r1 r2 f q1; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel2 : r2^2 + r3 = f*q2 := by unfold r2 r3 f q2; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel3 : r3^2 + r4 = f*q3 := by unfold r3 r4 f q3; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel4 : r4^2 + r5 = f*q4 := by unfold r4 r5 f q4; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel5 : r5^2 + r6 = f*q5 := by unfold r5 r6 f q5; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel6 : r6^2 + r7 = f*q6 := by unfold r6 r7 f q6; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel7 : r7^2 + r8 = f*q7 := by unfold r7 r8 f q7; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel8 : r8^2 + r9 = f*q8 := by unfold r8 r9 f q8; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel9 : r9^2 + r10 = f*q9 := by unfold r9 r10 f q9; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem rel10 : r10^2 + r11 = f*q10 := by unfold r10 r11 f q10; ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
#check Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
#check Polynomial.exists_monic_irreducible_factor


def charTwoPoly : (2 : P) = 0 := CharP.cast_eq_zero P 2
lemma square_step {a r s q : P} (h : f ∣ a + r) (hr : r^2 + s = f*q) :
    f ∣ a^2 + s := by
  have h1 : f ∣ (a+r)^2 := dvd_pow h (by norm_num)
  have h2 : f ∣ r^2+s := ⟨q, hr⟩
  have h3 : f ∣ (a+r)^2 + (r^2+s) := dvd_add h1 h2
  have heq : (a+r)^2 + (r^2+s) = a^2+s := by
    ring_nf
    simp [c2,c3,c4,c5,c6,c7,c8]
  rw [heq] at h3
  exact h3

lemma Xpow_square (n : Nat) : ((X : P)^(2^n))^2 = (X : P)^(2^(n+1)) := by
  rw [← pow_mul, Nat.pow_succ]

theorem f_dvd_frob_plus : f ∣ X^(2^11 : Nat) + X := by
  have h0 : f ∣ (X : P)^(2^0 : Nat) + r0 := by
    have hx : (X : P) + X = 0 := by
      have ht := congrArg (fun z : P => z * X) c2
      simpa [two_mul] using ht
    have he : (X : P)^(2^0 : Nat) + r0 = 0 := by simpa [r0] using hx
    rw [he]
    exact dvd_zero f
  have h1 : f ∣ (X : P)^(2^1 : Nat) + r1 := by
    have h := square_step h0 rel0
    simpa only [Xpow_square] using h
  have h2 : f ∣ (X : P)^(2^2 : Nat) + r2 := by
    have h := square_step h1 rel1
    simpa only [Xpow_square] using h
  have h3 : f ∣ (X : P)^(2^3 : Nat) + r3 := by
    have h := square_step h2 rel2
    simpa only [Xpow_square] using h
  have h4 : f ∣ (X : P)^(2^4 : Nat) + r4 := by
    have h := square_step h3 rel3
    simpa only [Xpow_square] using h
  have h5 : f ∣ (X : P)^(2^5 : Nat) + r5 := by
    have h := square_step h4 rel4
    simpa only [Xpow_square] using h
  have h6 : f ∣ (X : P)^(2^6 : Nat) + r6 := by
    have h := square_step h5 rel5
    simpa only [Xpow_square] using h
  have h7 : f ∣ (X : P)^(2^7 : Nat) + r7 := by
    have h := square_step h6 rel6
    simpa only [Xpow_square] using h
  have h8 : f ∣ (X : P)^(2^8 : Nat) + r8 := by
    have h := square_step h7 rel7
    simpa only [Xpow_square] using h
  have h9 : f ∣ (X : P)^(2^9 : Nat) + r9 := by
    have h := square_step h8 rel8
    simpa only [Xpow_square] using h
  have h10 : f ∣ (X : P)^(2^10 : Nat) + r10 := by
    have h := square_step h9 rel9
    simpa only [Xpow_square] using h
  have h11 : f ∣ (X : P)^(2^11 : Nat) + r11 := by
    have h := square_step h10 rel10
    simpa only [Xpow_square] using h
  simpa only [r11] using h11
theorem f_dvd_frob_sub : f ∣ (X : P)^(2^11 : Nat) - X := by
  have h := f_dvd_frob_plus
  have hneg : -(X : P) = X := by
    have htwo : (2 : P) = 0 := CharP.cast_eq_zero P 2
    have hx : (X : P) + X = 0 := by
      have hx' := congrArg (fun z : P => z * X) htwo
      simpa [two_mul] using hx'
    exact neg_eq_of_add_eq_zero_left hx
  convert h using 1 <;> simp [sub_eq_add_neg, hneg]
#check neg_eq_of_add_eq_zero_left
#print axioms f_dvd_frob_plus
#print axioms f_dvd_frob_sub








lemma c2F : (2 : F) = 0 := ZMod.natCast_self 2
lemma f_no_roots (x : F) : eval x f ≠ 0 := by
  have hv : x.val = 0 ∨ x.val = 1 := by have hxlt := ZMod.val_lt x; omega
  rcases hv with hv | hv
  · have hx : x = 0 := by
      apply ZMod.val_injective 2
      simpa [hv]
    subst x
    simp [f, eval_add, eval_pow, eval_X, eval_one]
  · have hx : x = 1 := by
      apply ZMod.val_injective 2
      rw [hv]
      exact ZMod.val_cast_of_lt (by norm_num : 1 < 2)
    subst x
    rw [f, eval_add, eval_add, eval_pow, eval_X, eval_pow, eval_X, eval_one]
    rw [one_pow, one_pow]
    have htwo : (1:F) + 1 = 0 := by change (2:F)=0; exact c2F
    rw [show (1:F)+(1:F)+(1:F) = ((1:F)+(1:F))+1 by rfl, htwo]
    norm_num


lemma f_irreducible : Irreducible f := by
  have hfmonic : f.Monic := by unfold f; norm_num only; monicity <;> norm_num
  have hfdeg : f.natDegree = 11 := by
    unfold f
    rw [add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 11
    · have hsmall : ((X : P)^2 + 1).natDegree = 2 := by
        simpa using (Polynomial.natDegree_X_pow_add_C (n := 2) (r := (1 : F)))
      rw [Polynomial.natDegree_X_pow, hsmall]
      norm_num
  have hf0 : f ≠ 0 := by intro hz; rw [hz] at hfdeg; norm_num at hfdeg
  have hfne : f ≠ 1 := by
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
  have hqNat : q.natDegree ≤ 5 := by
    rw [Polynomial.degree_eq_natDegree hq0] at hqdeg
    rw [hfdeg] at hqdeg
    norm_num at hqdeg
    exact_mod_cast hqdeg
  have hgNat : g.natDegree ≤ q.natDegree := Polynomial.natDegree_le_of_dvd hgq hq0
  have hgBound : g.natDegree ≤ 5 := hgNat.trans hqNat
  have hgfrob : g ∣ (X : P) ^ (Nat.card F) ^ 11 - X := by
    have hgF : g ∣ f := dvd_trans hgq hqf
    have := dvd_trans hgF f_dvd_frob_sub
    simpa [Nat.card_eq_fintype_card, ZMod.card] using this
  have hdiv : g.natDegree ∣ 11 :=
    (hgirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 11)).2 hgfrob
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp hdiv with hone | h11
  · have hgdeg1 : g.natDegree = 1 := hone
    rcases (Polynomial.natDegree_eq_one).mp hgdeg1 with ⟨a, ha, b, hrepr⟩
    let x : F := -b / a
    have hroot : g.IsRoot x := by
      change eval x g = 0
      rw [← hrepr, eval_add, eval_mul, eval_C, eval_X, eval_C]
      dsimp [x]
      field_simp [ha] <;> ring_nf <;> simp [c2F]
    have hfroot : f.IsRoot x := hroot.dvd (dvd_trans hgq hqf)
    exact f_no_roots x hfroot
  · omega









#print axioms f_irreducible
#print axioms f_no_roots
