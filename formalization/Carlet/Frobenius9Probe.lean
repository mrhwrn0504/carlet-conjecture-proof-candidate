import Carlet.Frobenius17Probe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def f9 : P17 := X^9 + X + 1
def r9_0 : P17 := X^1
def r9_1 : P17 := X^2
def r9_2 : P17 := X^4
def r9_3 : P17 := X^8
def r9_4 : P17 := X^7 + X^8
def r9_5 : P17 := X^5 + X^6 + X^7 + X^8
def r9_6 : P17 := X^1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8
def r9_7 : P17 := X^1 + X^3 + X^5 + X^7
def r9_8 : P17 := X^1 + X^5
def r9_9 : P17 := X^1
def q9_0 : P17 := 0
def q9_1 : P17 := 0
def q9_2 : P17 := 0
def q9_3 : P17 := X^7
def q9_4 : P17 := X^5 + X^7
def q9_5 : P17 := X^1 + X^3 + X^5 + X^7
def q9_6 : P17 := X^1 + X^3 + X^5 + X^7
def q9_7 : P17 := X^1 + X^5
def q9_8 : P17 := X^1
lemma f9_rel_0 : r9_0^2 + r9_1 = f9*q9_0 := by
  unfold r9_0 r9_1 f9 q9_0
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_1 : r9_1^2 + r9_2 = f9*q9_1 := by
  unfold r9_1 r9_2 f9 q9_1
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_2 : r9_2^2 + r9_3 = f9*q9_2 := by
  unfold r9_2 r9_3 f9 q9_2
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_3 : r9_3^2 + r9_4 = f9*q9_3 := by
  unfold r9_3 r9_4 f9 q9_3
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_4 : r9_4^2 + r9_5 = f9*q9_4 := by
  unfold r9_4 r9_5 f9 q9_4
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_5 : r9_5^2 + r9_6 = f9*q9_5 := by
  unfold r9_5 r9_6 f9 q9_5
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_6 : r9_6^2 + r9_7 = f9*q9_6 := by
  unfold r9_6 r9_7 f9 q9_6
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_7 : r9_7^2 + r9_8 = f9*q9_7 := by
  unfold r9_7 r9_8 f9 q9_7
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_rel_8 : r9_8^2 + r9_9 = f9*q9_8 := by
  unfold r9_8 r9_9 f9 q9_8
  ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_bezout : (X^6+X^5+X^3+X^2+1)*f9 + (X^7+X^6+X^4+X^3+X+1)*((X:P17)^8+X) = 1 := by
  unfold f9; ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
lemma f9_square_step {a r s q:P17} (h:f9∣a+r) (hr:r^2+s=f9*q) : f9∣a^2+s := by
  have h1:f9∣(a+r)^2 := dvd_pow h (by norm_num)
  have h2:f9∣r^2+s := ⟨q,hr⟩
  have h3:f9∣(a+r)^2+(r^2+s) := dvd_add h1 h2
  have heq:(a+r)^2+(r^2+s)=a^2+s := by ring_nf <;> simp [c2_17]
  rw [heq] at h3
  exact h3
theorem f9_dvd_frob_plus : f9 ∣ (X:P17)^(2^9:Nat)+X := by
  have h0 : f9 ∣ (X:P17)^(2^0:Nat)+r9_0 := by
    have hx:(X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
    have he:(X:P17)^(2^0:Nat)+r9_0=0 := by simpa [r9_0] using hx
    rw [he]; exact dvd_zero f9
  have h1 : f9 ∣ (X:P17)^(2^1:Nat)+r9_1 := by
    have h:=f9_square_step h0 f9_rel_0
    simpa only [Xpow_square_17] using h
  have h2 : f9 ∣ (X:P17)^(2^2:Nat)+r9_2 := by
    have h:=f9_square_step h1 f9_rel_1
    simpa only [Xpow_square_17] using h
  have h3 : f9 ∣ (X:P17)^(2^3:Nat)+r9_3 := by
    have h:=f9_square_step h2 f9_rel_2
    simpa only [Xpow_square_17] using h
  have h4 : f9 ∣ (X:P17)^(2^4:Nat)+r9_4 := by
    have h:=f9_square_step h3 f9_rel_3
    simpa only [Xpow_square_17] using h
  have h5 : f9 ∣ (X:P17)^(2^5:Nat)+r9_5 := by
    have h:=f9_square_step h4 f9_rel_4
    simpa only [Xpow_square_17] using h
  have h6 : f9 ∣ (X:P17)^(2^6:Nat)+r9_6 := by
    have h:=f9_square_step h5 f9_rel_5
    simpa only [Xpow_square_17] using h
  have h7 : f9 ∣ (X:P17)^(2^7:Nat)+r9_7 := by
    have h:=f9_square_step h6 f9_rel_6
    simpa only [Xpow_square_17] using h
  have h8 : f9 ∣ (X:P17)^(2^8:Nat)+r9_8 := by
    have h:=f9_square_step h7 f9_rel_7
    simpa only [Xpow_square_17] using h
  have h9 : f9 ∣ (X:P17)^(2^9:Nat)+r9_9 := by
    have h:=f9_square_step h8 f9_rel_8
    simpa only [Xpow_square_17] using h
  simpa [r9_9] using h9
theorem f9_dvd_frob_sub : f9 ∣ (X:P17)^(2^9:Nat)-X := by
  have h := f9_dvd_frob_plus
  have hneg : -(X:P17) = X := by
    have hx : (X:P17) + X = 0 := by
      have ht := congrArg (fun z:P17 => z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  convert h using 1 <;> simp [sub_eq_add_neg, hneg]
lemma f9_irreducible : Irreducible f9 := by
  have hm : f9.Monic := by unfold f9; monicity <;> norm_num
  have hd : f9.natDegree = 9 := by
    have hs : ((X:P17)+1).natDegree ≤ 1 := by
      calc
        _ ≤ max ((X:P17).natDegree) (1:P17).natDegree := Polynomial.natDegree_add_le _ _
        _ = 1 := by simp
    have hp : ((X:P17)^9).natDegree = 9 := Polynomial.natDegree_X_pow 9
    have hs' : ((X:P17)+1).natDegree < ((X:P17)^9).natDegree := by rw [hp]; omega
    have he : f9 = (X:P17)^9 + (X+1) := by unfold f9; ring
    rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
    exact hp
  have h0 : f9 ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
  have hne : f9 ≠ 1 := by
    intro h
    have hh := congrArg Polynomial.natDegree h
    rw [hd] at hh
    norm_num at hh
  rw [Polynomial.Monic.irreducible_iff_degree_lt hm hne]
  intro q hqdeg hqf
  by_contra hqnot
  obtain ⟨g, hgm, hgi, hgq⟩ := Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0 : q ≠ 0 := by intro h; subst q; simp at hqf; exact h0 hqf
  have hqN : q.natDegree ≤ 4 := by
    rw [Polynomial.degree_eq_natDegree hq0] at hqdeg
    rw [hd] at hqdeg
    norm_num at hqdeg
    exact_mod_cast hqdeg
  have hgB : g.natDegree ≤ 4 := (Polynomial.natDegree_le_of_dvd hgq hq0).trans hqN
  have hgf9 : g ∣ f9 := dvd_trans hgq hqf
  have hgf : g ∣ (X:P17)^(Nat.card F17)^9-X := by
    have hh := dvd_trans hgf9 f9_dvd_frob_sub
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hh
  have hdiv : g.natDegree ∣ 9 :=
    (hgi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n:=9)).2 hgf
  have hdiv3 : g.natDegree ∣ 3 := by
    interval_cases hdeg : g.natDegree <;> norm_num [hdeg] at *
  have hg8 : g ∣ (X:P17)^8-X := by
    have hh := (hgi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n:=3)).1 hdiv3
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hh
  have hneg : -(X:P17) = X := by
    have hx : (X:P17)+X=0 := by
      have ht := congrArg (fun z:P17 => z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  have hg8plus : g ∣ (X:P17)^8+X := by simpa [sub_eq_add_neg, hneg] using hg8
  have hone : g ∣ (1:P17) := by
    rw [← f9_bezout]
    exact dvd_add (dvd_mul_of_dvd_right hgf9 _) (dvd_mul_of_dvd_right hg8plus _)
  exact hgi.not_isUnit (isUnit_of_dvd_one hone)
#print axioms f9_bezout
#print axioms f9_dvd_frob_plus
#print axioms f9_irreducible
