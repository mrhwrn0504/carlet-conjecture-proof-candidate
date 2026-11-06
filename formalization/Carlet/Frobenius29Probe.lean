import Carlet.Frobenius29Rel1
import Carlet.Frobenius29Rel2
import Carlet.Frobenius29Rel3
import Carlet.Frobenius29Rel4
import Carlet.Frobenius29Rel5
import Carlet.Frobenius29Rel6
import Carlet.Frobenius23DegreeCriterionProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem f29_dvd_frob_sub : f29 ∣ frobPoly 29-X := by
  have h0 : f29 ∣ frobPoly 0+r29_0 := by
    rw [frobPoly_zero, r29_0]
    have hx : (X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
    simp only [pow_one]
    change f29 ∣ X+X
    rw [hx]; exact dvd_zero f29
  have h1 : f29 ∣ frobPoly 1+r29_1 := by
    have hs := f29_square_step h0 f29_rel_0
    have hsuc : (frobPoly (0))^2=frobPoly ((0)+1) := (frobPoly_succ (0)).symm
    have hi : (0)+1=1 := by omega
    have hp : (frobPoly (0))^2=frobPoly 1 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_1) hp).mp hs
  have h2 : f29 ∣ frobPoly 2+r29_2 := by
    have hs := f29_square_step h1 f29_rel_1
    have hsuc : (frobPoly (1))^2=frobPoly ((1)+1) := (frobPoly_succ (1)).symm
    have hi : (1)+1=2 := by omega
    have hp : (frobPoly (1))^2=frobPoly 2 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_2) hp).mp hs
  have h3 : f29 ∣ frobPoly 3+r29_3 := by
    have hs := f29_square_step h2 f29_rel_2
    have hsuc : (frobPoly (2))^2=frobPoly ((2)+1) := (frobPoly_succ (2)).symm
    have hi : (2)+1=3 := by omega
    have hp : (frobPoly (2))^2=frobPoly 3 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_3) hp).mp hs
  have h4 : f29 ∣ frobPoly 4+r29_4 := by
    have hs := f29_square_step h3 f29_rel_3
    have hsuc : (frobPoly (3))^2=frobPoly ((3)+1) := (frobPoly_succ (3)).symm
    have hi : (3)+1=4 := by omega
    have hp : (frobPoly (3))^2=frobPoly 4 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_4) hp).mp hs
  have h5 : f29 ∣ frobPoly 5+r29_5 := by
    have hs := f29_square_step h4 f29_rel_4
    have hsuc : (frobPoly (4))^2=frobPoly ((4)+1) := (frobPoly_succ (4)).symm
    have hi : (4)+1=5 := by omega
    have hp : (frobPoly (4))^2=frobPoly 5 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_5) hp).mp hs
  have h6 : f29 ∣ frobPoly 6+r29_6 := by
    have hs := f29_square_step h5 f29_rel_5
    have hsuc : (frobPoly (5))^2=frobPoly ((5)+1) := (frobPoly_succ (5)).symm
    have hi : (5)+1=6 := by omega
    have hp : (frobPoly (5))^2=frobPoly 6 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_6) hp).mp hs
  have h7 : f29 ∣ frobPoly 7+r29_7 := by
    have hs := f29_square_step h6 f29_rel_6
    have hsuc : (frobPoly (6))^2=frobPoly ((6)+1) := (frobPoly_succ (6)).symm
    have hi : (6)+1=7 := by omega
    have hp : (frobPoly (6))^2=frobPoly 7 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_7) hp).mp hs
  have h8 : f29 ∣ frobPoly 8+r29_8 := by
    have hs := f29_square_step h7 f29_rel_7
    have hsuc : (frobPoly (7))^2=frobPoly ((7)+1) := (frobPoly_succ (7)).symm
    have hi : (7)+1=8 := by omega
    have hp : (frobPoly (7))^2=frobPoly 8 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_8) hp).mp hs
  have h9 : f29 ∣ frobPoly 9+r29_9 := by
    have hs := f29_square_step h8 f29_rel_8
    have hsuc : (frobPoly (8))^2=frobPoly ((8)+1) := (frobPoly_succ (8)).symm
    have hi : (8)+1=9 := by omega
    have hp : (frobPoly (8))^2=frobPoly 9 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_9) hp).mp hs
  have h10 : f29 ∣ frobPoly 10+r29_10 := by
    have hs := f29_square_step h9 f29_rel_9
    have hsuc : (frobPoly (9))^2=frobPoly ((9)+1) := (frobPoly_succ (9)).symm
    have hi : (9)+1=10 := by omega
    have hp : (frobPoly (9))^2=frobPoly 10 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_10) hp).mp hs
  have h11 : f29 ∣ frobPoly 11+r29_11 := by
    have hs := f29_square_step h10 f29_rel_10
    have hsuc : (frobPoly (10))^2=frobPoly ((10)+1) := (frobPoly_succ (10)).symm
    have hi : (10)+1=11 := by omega
    have hp : (frobPoly (10))^2=frobPoly 11 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_11) hp).mp hs
  have h12 : f29 ∣ frobPoly 12+r29_12 := by
    have hs := f29_square_step h11 f29_rel_11
    have hsuc : (frobPoly (11))^2=frobPoly ((11)+1) := (frobPoly_succ (11)).symm
    have hi : (11)+1=12 := by omega
    have hp : (frobPoly (11))^2=frobPoly 12 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_12) hp).mp hs
  have h13 : f29 ∣ frobPoly 13+r29_13 := by
    have hs := f29_square_step h12 f29_rel_12
    have hsuc : (frobPoly (12))^2=frobPoly ((12)+1) := (frobPoly_succ (12)).symm
    have hi : (12)+1=13 := by omega
    have hp : (frobPoly (12))^2=frobPoly 13 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_13) hp).mp hs
  have h14 : f29 ∣ frobPoly 14+r29_14 := by
    have hs := f29_square_step h13 f29_rel_13
    have hsuc : (frobPoly (13))^2=frobPoly ((13)+1) := (frobPoly_succ (13)).symm
    have hi : (13)+1=14 := by omega
    have hp : (frobPoly (13))^2=frobPoly 14 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_14) hp).mp hs
  have h15 : f29 ∣ frobPoly 15+r29_15 := by
    have hs := f29_square_step h14 f29_rel_14
    have hsuc : (frobPoly (14))^2=frobPoly ((14)+1) := (frobPoly_succ (14)).symm
    have hi : (14)+1=15 := by omega
    have hp : (frobPoly (14))^2=frobPoly 15 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_15) hp).mp hs
  have h16 : f29 ∣ frobPoly 16+r29_16 := by
    have hs := f29_square_step h15 f29_rel_15
    have hsuc : (frobPoly (15))^2=frobPoly ((15)+1) := (frobPoly_succ (15)).symm
    have hi : (15)+1=16 := by omega
    have hp : (frobPoly (15))^2=frobPoly 16 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_16) hp).mp hs
  have h17 : f29 ∣ frobPoly 17+r29_17 := by
    have hs := f29_square_step h16 f29_rel_16
    have hsuc : (frobPoly (16))^2=frobPoly ((16)+1) := (frobPoly_succ (16)).symm
    have hi : (16)+1=17 := by omega
    have hp : (frobPoly (16))^2=frobPoly 17 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_17) hp).mp hs
  have h18 : f29 ∣ frobPoly 18+r29_18 := by
    have hs := f29_square_step h17 f29_rel_17
    have hsuc : (frobPoly (17))^2=frobPoly ((17)+1) := (frobPoly_succ (17)).symm
    have hi : (17)+1=18 := by omega
    have hp : (frobPoly (17))^2=frobPoly 18 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_18) hp).mp hs
  have h19 : f29 ∣ frobPoly 19+r29_19 := by
    have hs := f29_square_step h18 f29_rel_18
    have hsuc : (frobPoly (18))^2=frobPoly ((18)+1) := (frobPoly_succ (18)).symm
    have hi : (18)+1=19 := by omega
    have hp : (frobPoly (18))^2=frobPoly 19 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_19) hp).mp hs
  have h20 : f29 ∣ frobPoly 20+r29_20 := by
    have hs := f29_square_step h19 f29_rel_19
    have hsuc : (frobPoly (19))^2=frobPoly ((19)+1) := (frobPoly_succ (19)).symm
    have hi : (19)+1=20 := by omega
    have hp : (frobPoly (19))^2=frobPoly 20 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_20) hp).mp hs
  have h21 : f29 ∣ frobPoly 21+r29_21 := by
    have hs := f29_square_step h20 f29_rel_20
    have hsuc : (frobPoly (20))^2=frobPoly ((20)+1) := (frobPoly_succ (20)).symm
    have hi : (20)+1=21 := by omega
    have hp : (frobPoly (20))^2=frobPoly 21 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_21) hp).mp hs
  have h22 : f29 ∣ frobPoly 22+r29_22 := by
    have hs := f29_square_step h21 f29_rel_21
    have hsuc : (frobPoly (21))^2=frobPoly ((21)+1) := (frobPoly_succ (21)).symm
    have hi : (21)+1=22 := by omega
    have hp : (frobPoly (21))^2=frobPoly 22 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_22) hp).mp hs
  have h23 : f29 ∣ frobPoly 23+r29_23 := by
    have hs := f29_square_step h22 f29_rel_22
    have hsuc : (frobPoly (22))^2=frobPoly ((22)+1) := (frobPoly_succ (22)).symm
    have hi : (22)+1=23 := by omega
    have hp : (frobPoly (22))^2=frobPoly 23 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_23) hp).mp hs
  have h24 : f29 ∣ frobPoly 24+r29_24 := by
    have hs := f29_square_step h23 f29_rel_23
    have hsuc : (frobPoly (23))^2=frobPoly ((23)+1) := (frobPoly_succ (23)).symm
    have hi : (23)+1=24 := by omega
    have hp : (frobPoly (23))^2=frobPoly 24 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_24) hp).mp hs
  have h25 : f29 ∣ frobPoly 25+r29_25 := by
    have hs := f29_square_step h24 f29_rel_24
    have hsuc : (frobPoly (24))^2=frobPoly ((24)+1) := (frobPoly_succ (24)).symm
    have hi : (24)+1=25 := by omega
    have hp : (frobPoly (24))^2=frobPoly 25 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_25) hp).mp hs
  have h26 : f29 ∣ frobPoly 26+r29_26 := by
    have hs := f29_square_step h25 f29_rel_25
    have hsuc : (frobPoly (25))^2=frobPoly ((25)+1) := (frobPoly_succ (25)).symm
    have hi : (25)+1=26 := by omega
    have hp : (frobPoly (25))^2=frobPoly 26 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_26) hp).mp hs
  have h27 : f29 ∣ frobPoly 27+r29_27 := by
    have hs := f29_square_step h26 f29_rel_26
    have hsuc : (frobPoly (26))^2=frobPoly ((26)+1) := (frobPoly_succ (26)).symm
    have hi : (26)+1=27 := by omega
    have hp : (frobPoly (26))^2=frobPoly 27 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_27) hp).mp hs
  have h28 : f29 ∣ frobPoly 28+r29_28 := by
    have hs := f29_square_step h27 f29_rel_27
    have hsuc : (frobPoly (27))^2=frobPoly ((27)+1) := (frobPoly_succ (27)).symm
    have hi : (27)+1=28 := by omega
    have hp : (frobPoly (27))^2=frobPoly 28 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_28) hp).mp hs
  have h29 : f29 ∣ frobPoly 29+r29_29 := by
    have hs := f29_square_step h28 f29_rel_28
    have hsuc : (frobPoly (28))^2=frobPoly ((28)+1) := (frobPoly_succ (28)).symm
    have hi : (28)+1=29 := by omega
    have hp : (frobPoly (28))^2=frobPoly 29 := by rw [hi] at hsuc; exact hsuc
    exact (congrArg (fun z : P17 => f29 ∣ z+r29_29) hp).mp hs
  have h := h29
  have hr : r29_29=X := by norm_num [r29_29]
  rw [hr] at h
  have hx : (X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
  have hsub : frobPoly 29-X=frobPoly 29+X := by rw [sub_eq_add_neg, show -(X:P17)=X from neg_eq_of_add_eq_zero_left hx]
  rw [hsub]; exact h
lemma f29_bezout : (1)*f29+(X^1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^11 + X^12 + X^13 + X^14 + X^15 + X^16 + X^17 + X^18 + X^19 + X^20 + X^21 + X^22 + X^23 + X^24 + X^25 + X^26 + X^27)*((X:P17)^2+X)=1 := by unfold f29; ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem f29_irreducible : Irreducible f29 := by
  have hm : f29.Monic := by unfold f29; monicity <;> norm_num
  have hd : f29.natDegree=29 := by
    have hx : ((X:P17)^29).natDegree=29 := Polynomial.natDegree_X_pow 29
    have hsmall : (X^2+1:P17).natDegree≤2 := by
      calc _ ≤ max (X^2:P17).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
        _ = 2 := by simp
    have hlt : (X^2+1:P17).natDegree < ((X:P17)^29).natDegree := by rw [hx]; omega
    have he : f29=(X:P17)^29+(X^2+1) := by unfold f29; ring
    rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]; exact hx
  have hne : f29≠1 := by intro h; have hh:=congrArg Polynomial.natDegree h; rw [hd] at hh; norm_num at hh
  rw [Polynomial.Monic.irreducible_iff_degree_lt hm hne]
  intro q hqdeg hqf
  by_contra hqnot
  obtain ⟨g,hgm,hgi,hgq⟩ := Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0 : q≠0 := by intro h; subst q; simp at hqf; have hh : f29=0 := hqf; rw [hh] at hd; norm_num at hd
  have hqN : q.natDegree≤14 := by rw [Polynomial.degree_eq_natDegree hq0] at hqdeg; rw [hd] at hqdeg; norm_num at hqdeg; exact_mod_cast hqdeg
  have hgN : g.natDegree≤14 := (Polynomial.natDegree_le_of_dvd hgq hq0).trans hqN
  have hgf : g∣frobPoly 29-X := dvd_trans (dvd_trans hgq hqf) f29_dvd_frob_sub
  have hdiv : g.natDegree∣29 := (irreducible_degree_dvd_frobPoly g hgi 29).2 hgf
  have hp : Nat.Prime 29 := by norm_num
  have hdiv_cases : g.natDegree=1 ∨ g.natDegree=29 := (Nat.dvd_prime hp).mp hdiv
  have hdiv1 : g.natDegree=1 := by rcases hdiv_cases with h|h <;> omega
  have hlin : g∣(X:P17)^2-X := by
    have hh := (irreducible_degree_dvd_frobPoly g hgi 1).1 (by simpa [hdiv1])
    have hpow : frobPoly 1=(X:P17)^2 := by rw [frobPoly_eq_pow]; norm_num
    rw [hpow] at hh; exact hh
  have hx : (X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
  have hlin' : g∣(X:P17)^2+X := by simpa [sub_eq_add_neg, show -(X:P17)=X from neg_eq_of_add_eq_zero_left hx] using hlin
  have hgf : g∣f29 := dvd_trans hgq hqf
  have hone : g∣(1:P17) := by rw [← f29_bezout]; exact dvd_add (dvd_mul_of_dvd_right hgf _) (dvd_mul_of_dvd_right hlin' _) 
  exact hgi.not_isUnit (isUnit_of_dvd_one hone)
#print axioms f29_dvd_frob_sub
#print axioms f29_irreducible
