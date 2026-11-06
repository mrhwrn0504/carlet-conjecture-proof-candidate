import Carlet.K4ASWeierstrassGenericInjectionProbe
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.haveILetI false

namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

noncomputable def k4ASWFullTarget (A B : K) :=
  Sum (k4ASWSourcePairs A B)
    (Sum (k4ASW_xSpecialPairs A B) (k4ASW_ySpecialPairs A B))

noncomputable instance k4ASWFullTargetFintype (A B : K) :
    Fintype (k4ASWFullTarget A B) := by
  unfold k4ASWFullTarget
  infer_instance

noncomputable def k4ASWFullEncode
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (p : k4ASWeierstrassPairs A B) :
    k4ASWFullTarget A B := by
  classical
  by_cases hg : p.val.1+k4ASC A B ≠ 0 ∧
      p.val.2+A+k4ASC A B ≠ 0
  · exact Sum.inl
      (k4ASWGenericToSource n hn hfinrank A B ⟨p,hg⟩)
  · by_cases hx : p.val.1+k4ASC A B=0
    · have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
      have hx' : p.val.1=A^2+B := by
        calc
          p.val.1 = p.val.1+k4ASC A B+k4ASC A B := by
            dsimp [k4ASC]
            calc
              _ = p.val.1+(2:K)*(A^2+B) := by rw [h2]; simp
              _ = _ := by ring
          _ = A^2+B := by rw [hx]; simp [k4ASC]
      exact Sum.inr (Sum.inl ⟨p,hx'⟩)
    · have hy : p.val.2+A+k4ASC A B=0 := by
        by_contra hn
        exact hg ⟨hx,hn⟩
      have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
      have hy0 : p.val.2+(A+k4ASC A B)=0 := by simpa [add_assoc] using hy
      have hy' : p.val.2=A+k4ASC A B := by
        calc
          p.val.2 = p.val.2+(A+k4ASC A B)+(A+k4ASC A B) := by
            calc
              _ = p.val.2+(2:K)*(A+k4ASC A B) := by rw [h2]; simp
              _ = _ := by ring
          _ = A+k4ASC A B := by rw [hy0]; simp
      exact Sum.inr (Sum.inr ⟨p,hy'⟩)

noncomputable def k4ASWFullDecode (A B : K) :
    k4ASWFullTarget A B → K×K
  | Sum.inl s =>
      (k4ASWeierstrassX A s.val.1 s.val.2,
       k4ASWeierstrassY A B s.val.1 s.val.2)
  | Sum.inr (Sum.inl p) => p.val.val
  | Sum.inr (Sum.inr p) => p.val.val

theorem k4ASWFullDecode_encode
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (p : k4ASWeierstrassPairs A B) :
    k4ASWFullDecode A B (k4ASWFullEncode n hn hfinrank A B p)=p.val := by
  classical
  by_cases hg : p.val.1+k4ASC A B ≠ 0 ∧
      p.val.2+A+k4ASC A B ≠ 0
  · have henc : k4ASWFullEncode n hn hfinrank A B p =
        Sum.inl (k4ASWGenericToSource n hn hfinrank A B ⟨p,hg⟩) := by
      simp [k4ASWFullEncode, hg]
      apply congrArg (fun s : k4ASWSourcePairs A B => Sum.inl s)
      exact Subtype.ext rfl
    rw [henc]
    simp only [k4ASWFullDecode]
    have hs := k4ASWGenericToSource_spec n hn hfinrank A B ⟨p,hg⟩
    exact Prod.ext hs.1 hs.2
  · have hng : ¬(p.val.1+k4ASC A B ≠ 0 ∧
        p.val.2+A+k4ASC A B ≠ 0) := hg
    by_cases hx : p.val.1+k4ASC A B=0
    · have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
      have hx' : p.val.1=A^2+B := by
        calc
          p.val.1 = p.val.1+k4ASC A B+k4ASC A B := by
            dsimp [k4ASC]
            calc
              _ = p.val.1+(2:K)*(A^2+B) := by rw [h2]; simp
              _ = _ := by ring
          _ = A^2+B := by rw [hx]; simp [k4ASC]
      have henc : k4ASWFullEncode n hn hfinrank A B p =
          Sum.inr (Sum.inl ⟨p,hx'⟩) := by
        simp [k4ASWFullEncode, hx]
        apply congrArg (fun s : k4ASW_xSpecialPairs A B => Sum.inr (Sum.inl s))
        exact Subtype.ext rfl
      rw [henc]
      rfl
    · have hy : p.val.2+A+k4ASC A B=0 := by
        by_contra hn
        exact hng ⟨hx,hn⟩
      have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
      have hy0 : p.val.2+(A+k4ASC A B)=0 := by simpa [add_assoc] using hy
      have hy' : p.val.2=A+k4ASC A B := by
        calc
          p.val.2 = p.val.2+(A+k4ASC A B)+(A+k4ASC A B) := by
            calc
              _ = p.val.2+(2:K)*(A+k4ASC A B) := by rw [h2]; simp
              _ = _ := by ring
          _ = A+k4ASC A B := by rw [hy0]; simp
      have henc : k4ASWFullEncode n hn hfinrank A B p =
          Sum.inr (Sum.inr ⟨p,hy'⟩) := by
        simp [k4ASWFullEncode, hx, hy]
        apply congrArg (fun s : k4ASW_ySpecialPairs A B => Sum.inr (Sum.inr s))
        exact Subtype.ext rfl
      rw [henc]
      rfl

theorem k4ASWFullEncode_injective
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) :
    Function.Injective (k4ASWFullEncode n hn hfinrank A B) := by
  intro p q hpq
  have h := congrArg (k4ASWFullDecode A B) hpq
  rw [k4ASWFullDecode_encode, k4ASWFullDecode_encode] at h
  apply Subtype.ext
  exact h

theorem k4ASWeierstrassPairs_card_le_source_add_five
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) :
    Fintype.card (k4ASWeierstrassPairs A B) ≤
      Fintype.card (k4ASWSourcePairs A B)+5 := by
  classical
  have hinj := k4ASWFullEncode_injective n hn hfinrank A B
  have hcard := Fintype.card_le_of_injective
    (k4ASWFullEncode n hn hfinrank A B) hinj
  change Fintype.card (k4ASWeierstrassPairs A B) ≤
    Fintype.card (Sum (k4ASWSourcePairs A B)
      (Sum (k4ASW_xSpecialPairs A B) (k4ASW_ySpecialPairs A B))) at hcard
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  have hx := k4ASW_xSpecialPairs_card_le_two A B
  have hy := k4ASW_ySpecialPairs_card_le_three A B
  omega

theorem k4ASWSourcePairs_card_lower_of_hasse
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hnorm : A^2+A*B+B^2 ≠ 0) :
    (Fintype.card K : ℝ)-2*Real.sqrt (Fintype.card K : ℝ)-5 ≤
      Fintype.card (k4ASWSourcePairs A B) := by
  classical
  letI := k4ASWeierstrassPointFintype A B hnorm
  have hcount := k4ASWeierstrassCurve_pointCount A B hnorm
  have hhasse := k4ASWeierstrassCurve_hasse A B hnorm
  have hpairs := k4ASWeierstrassPairs_card_le_source_add_five
    n hn hfinrank A B
  have hlower :
      (Fintype.card K : ℝ)-2*Real.sqrt (Fintype.card K : ℝ) ≤
      (Fintype.card (k4ASWeierstrassPairs A B) : ℝ) := by
    rw [abs_le] at hhasse
    have hleft := hhasse.1
    rw [hcount] at hleft
    norm_num at hleft ⊢
    linarith
  have hpairsR :
      (Fintype.card (k4ASWeierstrassPairs A B) : ℝ) ≤
        (Fintype.card (k4ASWSourcePairs A B) : ℝ)+5 := by
    exact_mod_cast hpairs
  linarith

#print axioms k4ASWeierstrassPairs_card_le_source_add_five
#print axioms k4ASWSourcePairs_card_lower_of_hasse

end Carlet
