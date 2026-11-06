import Carlet.F19NamedIterBridge
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Polynomial
noncomputable section
lemma f19_frob_plus_to_sub (n : Nat) (h : f19Frob ∣ (X:P19Frob)^(2^n)+X) : f19Frob ∣ (X:P19Frob)^(2^n)-X := by
  have hx : (X:P19Frob)+X=0 := by
    have ht := congrArg (fun z:P19Frob => z*X) c2_19
    simpa [two_mul] using ht
  have hneg : -(X:P19Frob)=X := neg_eq_of_add_eq_zero_left hx
  simpa [sub_eq_add_neg, hneg] using h
lemma f19_frob_card (n : Nat) (h : f19Frob ∣ (X:P19Frob)^(2^n)-X) :
    f19Frob ∣ (X:P19Frob)^(Nat.card F19)^n-X := by
  simpa [Nat.card_eq_fintype_card, ZMod.card] using h
lemma f19_no_roots (x:F19) : eval x f19Frob ≠ 0 := by
  have hv : x.val=0 ∨ x.val=1 := by have hx:=ZMod.val_lt x; omega
  rcases hv with hv|hv
  · have hx:x=0 := by apply ZMod.val_injective 2; simpa [hv]
    subst x; simp [f19Frob]
  · have hx:x=1 := by apply ZMod.val_injective 2; rw [hv]; exact ZMod.val_cast_of_lt (by norm_num : (1:Nat)<2)
    subst x
    simp only [f19Frob, eval_add, eval_pow, eval_X, eval_one]
    have h11 : (1:F19) + 1 = 0 := by
      calc
        (1:F19) + 1 = (2:F19) := by norm_num [two_mul]
        _ = 0 := c2_F19
    simp only [f19Frob, eval_add, eval_pow, eval_X, eval_one, one_pow]
    simp [h11]
lemma f19_irreducible : Irreducible f19Frob := by
  have hm:f19Frob.Monic := by unfold f19Frob; monicity <;> norm_num
  have hd:f19Frob.natDegree=19 := by
    have hplus : ((X:P19Frob)+1).natDegree ≤ 1 := by
      calc
        _ ≤ max (X:P19Frob).natDegree (1:P19Frob).natDegree := Polynomial.natDegree_add_le _ _
        _ = 1 := by simp
    have h2 : ((X:P19Frob)^2+((X:P19Frob)+1)).natDegree ≤ 2 := by
      calc
        _ ≤ max ((X:P19Frob)^2).natDegree ((X:P19Frob)+1).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by simp only [Polynomial.natDegree_X_pow]; omega
    have hlow : ((X:P19Frob)^5+((X:P19Frob)^2+((X:P19Frob)+1))).natDegree ≤ 5 := by
      calc
        _ ≤ max ((X:P19Frob)^5).natDegree ((X:P19Frob)^2+((X:P19Frob)+1)).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 5 := by simp only [Polynomial.natDegree_X_pow]; omega
    have hp:((X:P19Frob)^19).natDegree=19 := Polynomial.natDegree_X_pow 19
    have hs':((X:P19Frob)^5+((X:P19Frob)^2+((X:P19Frob)+1))).natDegree<((X:P19Frob)^19).natDegree := by rw [hp]; omega
    unfold f19Frob; rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']; exact hp
  have h0:f19Frob≠0 := by intro h; rw [h] at hd; norm_num at hd
  have hne:f19Frob≠1 := by intro h; have hh:=congrArg Polynomial.natDegree h; rw [hd] at hh; norm_num at hh
  rw [Polynomial.Monic.irreducible_iff_degree_lt hm hne]
  intro q hqdeg hqf; by_contra hqnot
  obtain ⟨g,hgm,hgi,hgq⟩:=Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0:q≠0 := by intro h; subst q; simp at hqf; exact h0 hqf
  have hqN:q.natDegree≤9 := by rw [Polynomial.degree_eq_natDegree hq0] at hqdeg; rw [hd] at hqdeg; norm_num at hqdeg; exact_mod_cast hqdeg
  have hgN:g.natDegree≤q.natDegree := Polynomial.natDegree_le_of_dvd hgq hq0
  have hgB:g.natDegree≤9 := hgN.trans hqN
  have hgf:g∣(X:P19Frob)^(Nat.card F19)^19-X := dvd_trans (dvd_trans hgq hqf) (f19_frob_card 19 (f19_frob_plus_to_sub 19 f19_dvd_frob_iter_plus))
  have hdiv:g.natDegree∣19 := (hgi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n:=19)).2 hgf
  rcases (Nat.dvd_prime (by norm_num:Nat.Prime 19)).mp hdiv with hone|h19
  · have hgd:g.natDegree=1:=hone
    rcases (Polynomial.natDegree_eq_one).mp hgd with ⟨a,ha,b,hrepr⟩
    let root:F19 := -b/a
    have hr:g.IsRoot root := by change eval root g=0; rw [←hrepr,eval_add,eval_mul,eval_C,eval_X,eval_C]; dsimp [root]; field_simp [ha] <;> ring_nf <;> simp
    exact f19_no_roots root (hr.dvd (dvd_trans hgq hqf))
  · omega
#print axioms f19_irreducible
