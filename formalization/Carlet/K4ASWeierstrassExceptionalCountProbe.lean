import Carlet.K4ASWeierstrassReverseNumeratorProbe
import Mathlib.Tactic

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

noncomputable def k4ASWQuadratic (C : K) : K[X] := X^2+X+Polynomial.C C

omit [CharP K 2] in
theorem k4ASWQuadratic_roots_card_le_two (C : K) :
    Fintype.card {x : K // (k4ASWQuadratic C).eval x = 0} ≤ 2 := by
  classical
  have hmono : (k4ASWQuadratic C).Monic := by
    unfold k4ASWQuadratic
    monicity
    norm_num
  have hdegree : (k4ASWQuadratic C).natDegree ≤ 2 := by
    unfold k4ASWQuadratic
    have hsum : (X^2+X : K[X]).natDegree ≤ 2 := by
      calc
        _ ≤ max (X^2 : K[X]).natDegree X.natDegree :=
          Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by simp
    calc
      _ ≤ max (X^2+X : K[X]).natDegree (Polynomial.C C).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by simp [hsum]
  have hp : k4ASWQuadratic C ≠ 0 := hmono.ne_zero
  let R := (k4ASWQuadratic C).roots.toFinset
  have heq : ∀ x : K, (k4ASWQuadratic C).eval x = 0 ↔ x ∈ R := by
    intro x
    constructor
    · intro hx
      apply Multiset.mem_toFinset.mpr
      exact (Polynomial.mem_roots hp).2 hx
    · intro hx
      exact (Polynomial.mem_roots hp).1 (Multiset.mem_toFinset.mp hx)
  let e : {x : K // (k4ASWQuadratic C).eval x = 0} ≃ {x : K // x ∈ R} :=
    Equiv.subtypeEquivProp (by
      funext x
      exact propext (heq x))
  have hrootcard : Fintype.card {x : K // x ∈ R}=R.card := by
    rw [Fintype.card_subtype]
    simp
  calc
    Fintype.card {x : K // (k4ASWQuadratic C).eval x = 0} =
        Fintype.card {x : K // x ∈ R} := Fintype.card_congr e
    _ = R.card := hrootcard
    _ ≤ (k4ASWQuadratic C).roots.card := Multiset.toFinset_card_le _
    _ ≤ (k4ASWQuadratic C).natDegree := Polynomial.card_roots' _
    _ ≤ 2 := hdegree

noncomputable def k4ASW_ySpecialPairs (A B : K) :=
  {p : k4ASWeierstrassPairs A B //
    p.val.2=A+k4ASC A B}

noncomputable instance k4ASW_ySpecialPairsFintype (A B : K) :
    Fintype (k4ASW_ySpecialPairs A B) := by
  classical
  unfold k4ASW_ySpecialPairs
  exact Fintype.ofFinite _

noncomputable def k4ASW_ySpecialEncode (A B : K)
    (p : k4ASW_ySpecialPairs A B) :
    Sum Unit {x : K // (k4ASWQuadratic (k4ASC A B)).eval x=0} := by
  classical
  by_cases hzero : p.val.val.1+k4ASC A B=0
  · exact Sum.inl ()
  · have hW : k4ASReverseWeierstrassRhs A B p.val.val.1
        (A+k4ASC A B) := by
      simpa [k4ASReverseWeierstrassRhs,k4ASC,p.property] using p.val.property
    have hclass := k4ASW_ySpecial_points_classified A B p.val.val.1 hW
    have hroot : p.val.val.1^2+p.val.val.1+k4ASC A B=0 := by
      rcases hclass with hbad | hgood
      · exact (hzero hbad).elim
      · exact hgood
    exact Sum.inr ⟨p.val.val.1, by simpa [k4ASWQuadratic] using hroot⟩

omit [Fintype K] in
theorem k4ASW_ySpecialEncode_injective (A B : K) :
    Function.Injective (k4ASW_ySpecialEncode A B) := by
  classical
  intro p q hpq
  have hfirst : p.val.val.1=q.val.val.1 := by
    by_cases hp : p.val.val.1+k4ASC A B=0
    · have hq : q.val.val.1+k4ASC A B=0 := by
        by_contra hn
        simp [k4ASW_ySpecialEncode,hp,hn] at hpq
      linear_combination hp-hq
    · have hq : q.val.val.1+k4ASC A B≠0 := by
        intro hz
        simp [k4ASW_ySpecialEncode,hp,hz] at hpq
      have heq :
          (⟨p.val.val.1, by
            have hW : k4ASReverseWeierstrassRhs A B p.val.val.1
                (A+k4ASC A B) := by
              simpa [k4ASReverseWeierstrassRhs,k4ASC,p.property]
                using p.val.property
            have hc := k4ASW_ySpecial_points_classified A B p.val.val.1 hW
            rcases hc with hz | hr
            · exact (hp hz).elim
            · simpa [k4ASWQuadratic] using hr⟩ :
            {x : K // (k4ASWQuadratic (k4ASC A B)).eval x=0}) =
          ⟨q.val.val.1, by
            have hW : k4ASReverseWeierstrassRhs A B q.val.val.1
                (A+k4ASC A B) := by
              simpa [k4ASReverseWeierstrassRhs,k4ASC,q.property]
                using q.val.property
            have hc := k4ASW_ySpecial_points_classified A B q.val.val.1 hW
            rcases hc with hz | hr
            · exact (hq hz).elim
            · simpa [k4ASWQuadratic] using hr⟩ := by
        simpa [k4ASW_ySpecialEncode,hp,hq] using hpq
      exact congrArg Subtype.val heq
  have hsecond : p.val.val.2=q.val.val.2 := by
    rw [p.property,q.property]
  have hpair : p.val.val=q.val.val := Prod.ext hfirst hsecond
  apply Subtype.ext
  apply Subtype.ext
  exact hpair

theorem k4ASW_ySpecialPairs_card_le_three (A B : K) :
    Fintype.card (k4ASW_ySpecialPairs A B) ≤ 3 := by
  classical
  have hinj := k4ASW_ySpecialEncode_injective A B
  have hle := Fintype.card_le_of_injective (k4ASW_ySpecialEncode A B) hinj
  have hroots := k4ASWQuadratic_roots_card_le_two (k4ASC A B)
  have hle' : Fintype.card (k4ASW_ySpecialPairs A B) ≤
      Fintype.card Unit + Fintype.card
        {x : K // (k4ASWQuadratic (k4ASC A B)).eval x=0} := by
    simpa [Fintype.card_sum] using hle
  have hle'' : Fintype.card (k4ASW_ySpecialPairs A B) ≤
      1 + Fintype.card
        {x : K // (k4ASWQuadratic (k4ASC A B)).eval x=0} := by
    simpa using hle'
  omega

noncomputable def k4ASW_xSpecialPairs (A B : K) :=
  {p : k4ASWeierstrassPairs A B // p.val.1=A^2+B}

noncomputable instance k4ASW_xSpecialPairsFintype (A B : K) :
    Fintype (k4ASW_xSpecialPairs A B) := by
  classical
  unfold k4ASW_xSpecialPairs
  exact Fintype.ofFinite _

noncomputable def k4ASW_xSpecialEncode (A B : K)
    (p : k4ASW_xSpecialPairs A B) :
    {y : K // y ∈ ({-(A+k4ASC A B), -(A+B)} : Finset K)} := by
  classical
  refine ⟨p.val.val.2, ?_⟩
  have hW : k4ASReverseWeierstrassRhs A B (A^2+B) p.val.val.2 := by
    simpa [k4ASReverseWeierstrassRhs,k4ASC,p.property] using p.val.property
  rcases k4ASW_xSpecial_points_classified A B p.val.val.2 hW with h₁ | h₂
  · apply Finset.mem_insert.mpr
    left
    have h₁' : p.val.val.2+(A+k4ASC A B)=0 := by
      simpa [k4ASC,add_assoc] using h₁
    calc
      p.val.val.2 = p.val.val.2+(A+k4ASC A B)-(A+k4ASC A B) := by ring
      _ = 0-(A+k4ASC A B) := by rw [h₁']
      _ = -(A+k4ASC A B) := by simp
  · apply Finset.mem_insert.mpr
    right
    apply Finset.mem_singleton.mpr
    have h₂' : p.val.val.2+(A+B)=0 := by simpa [add_assoc] using h₂
    calc
      p.val.val.2 = p.val.val.2+(A+B)-(A+B) := by ring
      _ = 0-(A+B) := by rw [h₂']
      _ = -(A+B) := by simp

omit [Fintype K] in
theorem k4ASW_xSpecialEncode_injective (A B : K) :
    Function.Injective (k4ASW_xSpecialEncode A B) := by
  intro p q hpq
  have hy : p.val.val.2=q.val.val.2 := congrArg Subtype.val hpq
  have hx : p.val.val.1=q.val.val.1 := by rw [p.property,q.property]
  have hpair : p.val.val=q.val.val := Prod.ext hx hy
  apply Subtype.ext
  apply Subtype.ext
  exact hpair

theorem k4ASW_xSpecialPairs_card_le_two (A B : K) :
    Fintype.card (k4ASW_xSpecialPairs A B) ≤ 2 := by
  classical
  have hinj := k4ASW_xSpecialEncode_injective A B
  have hle := Fintype.card_le_of_injective (k4ASW_xSpecialEncode A B) hinj
  let S : Finset K := {-(A+k4ASC A B),-(A+B)}
  have htarget : Fintype.card
      {y : K // y ∈ S} ≤ 2 := by
    rw [Fintype.card_subtype]
    calc
      (Finset.univ.filter (fun y : K => y ∈ S)).card ≤ S.card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy
      _ ≤ 2 := by
        change ({-(A+k4ASC A B),-(A+B)} : Finset K).card ≤ 2
        calc
          _ ≤ ({-(A+B)} : Finset K).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
  exact le_trans hle htarget

#print axioms k4ASWQuadratic_roots_card_le_two
#print axioms k4ASW_ySpecialPairs_card_le_three
#print axioms k4ASW_xSpecialPairs_card_le_two

end Carlet
