import Carlet.K4NormOneParametrizationProbe
import Carlet.K4BadLocusSZProbe
import Carlet.SubspacePolynomial
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
local instance (E : Submodule (ZMod 2) K) : Fintype E := Fintype.ofFinite E
attribute [local instance] Classical.propDecidable

omit [Fintype K] in
private theorem k4_neg_eq_self_of_char_two (a : K) : -a = a := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have honeadd : (1 : K) + 1 = 0 := by
    have htwo' : (2 : K) = (1 : K) + 1 := by ring
    rw [htwo'] at htwo
    exact htwo
  have hnegone : (-1 : K) = 1 := by
    calc
      -1 = -1 + 0 := by simp
      _ = -1 + ((1 : K) + 1) := by rw [← honeadd]
      _ = 1 := by ring
  calc
    -a = (-1) * a := by ring
    _ = 1 * a := by rw [hnegone]
    _ = a := by simp

def k4TracePlaneEnumVal (t : K) (i : Fin 4) : K :=
  if i.val=0 then 0 else if i.val=1 then 1 else if i.val=2 then t else 1+t

def k4TracePlaneEnum (t : K) (i : Fin 4) : k4TracePlane t := by
  have h1 : (1:K) ∈ k4TracePlane t := by
    apply Submodule.subset_span
    simp
  have ht : t ∈ k4TracePlane t := by
    apply Submodule.subset_span
    simp
  refine ⟨k4TracePlaneEnumVal t i, ?_⟩
  fin_cases i
  · exact Submodule.zero_mem _
  · exact h1
  · exact ht
  · exact (k4TracePlane t).add_mem h1 ht

omit [Fintype K] in
theorem k4TracePlaneEnum_val (t : K) (i : Fin 4) :
    (k4TracePlaneEnum t i : K)=k4TracePlaneEnumVal t i := rfl

omit [Fintype K] in
theorem k4TracePlane_mem_enum (t : K)
    {x : K} (hx : x ∈ k4TracePlane t) :
    ∃ i : Fin 4, k4TracePlaneEnumVal t i=x := by
  have hxspan : x ∈ Submodule.span (ZMod 2) (insert (1:K) ({t}:Set K)) := by
    simpa [k4TracePlane] using hx
  obtain ⟨a,z,hz,hxEq⟩ := Submodule.mem_span_insert.mp hxspan
  rcases (mem_span_singleton_two t z).mp hz with hz0 | hzt
  · subst z
    by_cases ha : a=0
    · subst a
      refine ⟨0, ?_⟩
      simpa [k4TracePlaneEnumVal] using hxEq.symm
    · have ha1 : a=1 := zmodTwo_eq_one_of_ne_zero a ha
      subst a
      refine ⟨1, ?_⟩
      simpa [k4TracePlaneEnumVal] using hxEq.symm
  · subst z
    by_cases ha : a=0
    · subst a
      refine ⟨2, ?_⟩
      simpa [k4TracePlaneEnumVal] using hxEq.symm
    · have ha1 : a=1 := zmodTwo_eq_one_of_ne_zero a ha
      subst a
      refine ⟨3, ?_⟩
      simpa [k4TracePlaneEnumVal] using hxEq.symm

omit [Fintype K] in
theorem k4_one_add_t_eq_zero_implies_t_eq_one (t : K)
    (h : (1:K)+t=0) : t=1 := by
  have h' : (1:K)=-t := eq_neg_of_add_eq_zero_left h
  calc
    t=-t := (k4_neg_eq_self_of_char_two t).symm
    _=1 := h'.symm

omit [Fintype K] in
theorem k4TracePlaneEnum_injective (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    Function.Injective (k4TracePlaneEnum t) := by
  intro i j hij
  have h := congrArg (fun p : k4TracePlane t => (p:K)) hij
  have hval : k4TracePlaneEnumVal t i=k4TracePlaneEnumVal t j := by
    simpa only [k4TracePlaneEnum_val] using h
  clear h hij
  apply Fin.ext
  fin_cases i <;> fin_cases j <;> simp [k4TracePlaneEnumVal] at hval ⊢
  all_goals
    first
    | exact False.elim (ht0 hval.symm)
    | exact False.elim (ht0 hval)
    | exact False.elim (ht1 hval.symm)
    | exact False.elim (ht1 hval)
    | exact False.elim (ht1 (k4_one_add_t_eq_zero_implies_t_eq_one t hval.symm))
    | exact False.elim (ht1 (k4_one_add_t_eq_zero_implies_t_eq_one t hval))

omit [Fintype K] in
theorem k4TracePlaneEnum_surjective (t : K) :
    Function.Surjective (k4TracePlaneEnum t) := by
  intro x
  obtain ⟨i,hi⟩ := k4TracePlane_mem_enum t x.property
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi

noncomputable def k4TracePlaneFinFourEquiv (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    Fin 4 ≃ k4TracePlane t :=
  Equiv.ofBijective (k4TracePlaneEnum t)
    ⟨k4TracePlaneEnum_injective t ht0 ht1,
      k4TracePlaneEnum_surjective t⟩

theorem k4TracePlane_card_eq_four (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    Fintype.card (k4TracePlane t)=4 := by
  calc
    Fintype.card (k4TracePlane t)=Fintype.card (Fin 4) :=
      Fintype.card_congr (k4TracePlaneFinFourEquiv t ht0 ht1).symm
    _=4 := by simp

theorem k4TracePlane_joint_filter_eq_sixteen
    (t u v : K) (ht0 : t≠0) (ht1 : t≠1) :
    (∑ r : k4TracePlane t, traceCharacter ((r:K)*u)) *
      (∑ s : k4TracePlane t, traceCharacter ((s:K)*v)) =
      if (∀ a ∈ k4TracePlane t,
          Algebra.trace (ZMod 2) K (a*u)=0) ∧
         (∀ a ∈ k4TracePlane t,
          Algebra.trace (ZMod 2) K (a*v)=0)
      then 16 else 0 := by
  rw [k4TracePlane_joint_character_product,
    Nat.card_eq_fintype_card, k4TracePlane_card_eq_four t ht0 ht1]
  norm_num

def k4NormOneTraceGood (t : K) (p : k4NormOnePairs (K:=K)) : Prop :=
  (∀ a ∈ k4TracePlane t,
    Algebra.trace (ZMod 2) K (a*p.val.2)=0) ∧
  (∀ a ∈ k4TracePlane t,
    Algebra.trace (ZMod 2) K (a*(p.val.1+p.val.2))=0)

noncomputable instance k4NormOneTraceGoodFintype (t : K) :
    Fintype {p : k4NormOnePairs (K:=K) // k4NormOneTraceGood t p} := by
  classical
  exact Fintype.ofFinite _

theorem k4NormOneTraceGood_filter_card_identity (t : K) :
    (∑ p : k4NormOnePairs (K:=K),
      if k4NormOneTraceGood t p then (16:ℝ) else 0) =
      (Fintype.card {p : k4NormOnePairs (K:=K) // k4NormOneTraceGood t p} : ℝ)*16 := by
  classical
  let P : k4NormOnePairs (K:=K) → Prop := fun p => k4NormOneTraceGood t p
  let s : Finset (k4NormOnePairs (K:=K)) := Finset.univ.filter P
  calc
    _ = ∑ p ∈ s, (16:ℝ) := by
      simpa [s,P] using
        (Fintype.sum_ite_mem s (fun _ : k4NormOnePairs (K:=K) => (16:ℝ)))
    _ = (s.card:ℝ)*16 := by simp
    _ = (Fintype.card {p : k4NormOnePairs (K:=K) // P p}:ℝ)*16 := by
      have hsubcard :
          Fintype.card {p : k4NormOnePairs (K:=K) // P p}=s.card := by
        simpa [s,P] using (Fintype.card_subtype P)
      rw [← hsubcard]

theorem k4NormOneTraceGood_card_fourier_sum
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    (Fintype.card {p : k4NormOnePairs (K:=K) // k4NormOneTraceGood t p} : ℝ)*16 =
      ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        k4ASWFourierCoefficient (s:K) (r:K) := by
  calc
    _ = ∑ p : k4NormOnePairs (K:=K),
        if k4NormOneTraceGood t p then (16:ℝ) else 0 := by
      exact (k4NormOneTraceGood_filter_card_identity t).symm
    _ = ∑ p : k4NormOnePairs (K:=K),
        (∑ r : k4TracePlane t, traceCharacter ((r:K)*p.val.2)) *
        (∑ s : k4TracePlane t,
          traceCharacter ((s:K)*(p.val.1+p.val.2))) := by
      apply Fintype.sum_congr
      intro p
      by_cases hgood : k4NormOneTraceGood t p
      · have hc :
            (∀ a ∈ k4TracePlane t,
              Algebra.trace (ZMod 2) K (a*p.val.2)=0) ∧
            (∀ a ∈ k4TracePlane t,
              Algebra.trace (ZMod 2) K (a*(p.val.1+p.val.2))=0) := hgood
        rw [if_pos hgood, k4TracePlane_joint_filter_eq_sixteen t
          p.val.2 (p.val.1+p.val.2) ht0 ht1, if_pos hc]
      · have hc : ¬(
            (∀ a ∈ k4TracePlane t,
              Algebra.trace (ZMod 2) K (a*p.val.2)=0) ∧
            (∀ a ∈ k4TracePlane t,
              Algebra.trace (ZMod 2) K (a*(p.val.1+p.val.2))=0)) := hgood
        rw [if_neg hgood, k4TracePlane_joint_filter_eq_sixteen t
          p.val.2 (p.val.1+p.val.2) ht0 ht1, if_neg hc]
    _ = ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        k4ASWFourierCoefficient (s:K) (r:K) :=
      k4NormOne_joint_fourier_expansion n hn hfinrank t

theorem k4TracePlane_fourier_sum_lower
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    (Fintype.card K : ℝ)+1-30*Real.sqrt (Fintype.card K : ℝ)-60 ≤
      ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        k4ASWFourierCoefficient (s:K) (r:K) := by
  classical
  let α := k4TracePlane t × k4TracePlane t
  let f : α → ℝ := fun z =>
    k4ASWFourierCoefficient (z.2:K) (z.1:K)
  let z : α :=
    (⟨0, Submodule.zero_mem _⟩, ⟨0, Submodule.zero_mem _⟩)
  have hcard : Fintype.card α=16 := by
    simp [α, k4TracePlane_card_eq_four t ht0 ht1]
  have hzmem : z∈(Finset.univ : Finset α) := by simp
  have hzerof : f z=(Fintype.card K:ℝ)+1 := by
    simp [f,z,k4ASWFourierCoefficient,k4ASWFourierValue]
  have hrest :
      ∑ x ∈ (Finset.univ : Finset α).erase z, f x ≥
        (15:ℝ)*(-2*Real.sqrt (Fintype.card K:ℝ)-4) := by
    have hpoint : ∀ x ∈ (Finset.univ : Finset α).erase z,
        -2*Real.sqrt (Fintype.card K:ℝ)-4 ≤ f x := by
      intro x hx
      have hxne : x≠z := (Finset.mem_erase.mp hx).1
      have hpair : (x.1:K)≠0 ∨ (x.2:K)≠0 := by
        by_contra h
        have hfirst : (x.1:K)=0 := by
          by_contra hfirst
          exact h (Or.inl hfirst)
        have hsecond : (x.2:K)=0 := by
          by_contra hsecond
          exact h (Or.inr hsecond)
        apply hxne
        apply Prod.ext
        · exact Subtype.ext hfirst
        · exact Subtype.ext hsecond
      have hcoef := k4ASWFourierCoefficient_lower_of_hasse
        n hn hfinrank (x.2:K) (x.1:K) (Or.symm hpair)
      exact hcoef
    have hsum := Finset.sum_le_sum hpoint
    have herase : ((Finset.univ : Finset α).erase z).card=15 := by
      rw [Finset.card_erase_of_mem hzmem]
      simp [hcard]
    calc
      (15:ℝ)*(-2*Real.sqrt (Fintype.card K:ℝ)-4)
          = ∑ x ∈ (Finset.univ : Finset α).erase z,
              (-2*Real.sqrt (Fintype.card K:ℝ)-4) := by
            simp [herase]
            ring
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).erase z, f x := hsum
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset α) f hzmem
  have htotal :
      ∑ x : α, f x = f z + ∑ x ∈ (Finset.univ : Finset α).erase z, f x := by
    calc
      ∑ x : α, f x =
          (∑ x ∈ (Finset.univ : Finset α).erase z, f x)+f z := hsplit.symm
      _ = f z + ∑ x ∈ (Finset.univ : Finset α).erase z, f x := by ring
  have hbound := add_le_add_left hrest (f z)
  rw [hzerof] at hbound
  have hfinal :
      (Fintype.card K:ℝ)+1-30*Real.sqrt (Fintype.card K:ℝ)-60 ≤
        ∑ x : α, f x := by
    rw [htotal]
    nlinarith
  simpa [α,f,Fintype.sum_prod_type] using hfinal

theorem k4NormOneTraceGood_card_gt_two
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1)
    (hq : 2048 ≤ Fintype.card K) :
    2 < Fintype.card
      {p : k4NormOnePairs (K:=K) // k4NormOneTraceGood t p} := by
  let N := Fintype.card
    {p : k4NormOnePairs (K:=K) // k4NormOneTraceGood t p}
  have hsum := k4NormOneTraceGood_card_fourier_sum
    n hn hfinrank t ht0 ht1
  have hlow := k4TracePlane_fourier_sum_lower n hn hfinrank t ht0 ht1
  have hN :
      ((Fintype.card K:ℝ)+1-30*Real.sqrt (Fintype.card K:ℝ)-60)/16 ≤
        (N:ℝ) := by
    rw [← hsum] at hlow
    dsimp [N]
    nlinarith
  exact k4_normOne_fourConstraint_count_gt_two_with_fiber_loss
    (Fintype.card K) N hq hN

#print axioms k4TracePlane_mem_enum
#print axioms k4TracePlaneEnum_injective
#print axioms k4TracePlane_card_eq_four
#print axioms k4TracePlane_joint_filter_eq_sixteen
#print axioms k4NormOneTraceGood_filter_card_identity
#print axioms k4NormOneTraceGood_card_fourier_sum
#print axioms k4TracePlane_fourier_sum_lower
#print axioms k4NormOneTraceGood_card_gt_two

end Carlet
