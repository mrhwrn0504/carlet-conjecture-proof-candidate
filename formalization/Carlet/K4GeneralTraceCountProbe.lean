import Carlet.K4NormOneParametrizationProbe
import Carlet.K4NormOneCountArithmeticProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K]

attribute [local instance] Classical.propDecidable

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
local instance k4GeneralTraceFintype (E : Submodule (ZMod 2) K) :
    Fintype E := Fintype.ofFinite E

def k4GeneralTraceMulHom (E : Submodule (ZMod 2) K) (u : K) : E →ₗ[ZMod 2] K where
  toFun r := (r:K)*u
  map_add' r s := by simp [add_mul]
  map_smul' c r := by simp [Algebra.smul_def, mul_assoc]

theorem k4GeneralTrace_character_sum
    (E : Submodule (ZMod 2) K) (u : K) :
    (∑ r : E, traceCharacter ((r:K)*u)) =
      if ∀ a ∈ E, Algebra.trace (ZMod 2) K (a*u)=0
      then (Fintype.card E:ℝ) else 0 := by
  classical
  let ψ : AddChar E ℝ := traceCharacter.compAddMonoidHom
    (k4GeneralTraceMulHom E u).toAddMonoidHom
  have hzero : ψ=0 ↔ ∀ a ∈ E, Algebra.trace (ZMod 2) K (a*u)=0 := by
    constructor
    · intro h a ha
      have hh := congrArg (fun φ : AddChar E ℝ => φ ⟨a,ha⟩) h
      change traceCharacter (a*u)=1 at hh
      exact (traceCharacter_eq_one_iff _).mp hh
    · intro h
      apply AddChar.ext
      intro r
      change traceCharacter ((r:K)*u)=1
      exact (traceCharacter_eq_one_iff _).mpr (h (r:K) r.property)
  have hs := AddChar.sum_eq_ite ψ
  change (∑ r : E, ψ r) = if ψ=0 then (Fintype.card E:ℝ) else 0 at hs
  by_cases hψ : ψ=0
  · have htrace := hzero.mp hψ
    simp only [if_pos hψ] at hs
    simp only [if_pos htrace]
    simpa [ψ, AddChar.compAddMonoidHom_apply,
      LinearMap.toAddMonoidHom_coe, k4GeneralTraceMulHom] using hs
  · have htrace : ¬ ∀ a ∈ E, Algebra.trace (ZMod 2) K (a*u)=0 :=
      fun h => hψ (hzero.mpr h)
    simp only [if_neg hψ] at hs
    simp only [if_neg htrace]
    simpa [ψ, AddChar.compAddMonoidHom_apply,
      LinearMap.toAddMonoidHom_coe, k4GeneralTraceMulHom] using hs

theorem k4GeneralTrace_joint_filter
    (E : Submodule (ZMod 2) K) (u v : K) :
    (∑ r : E, traceCharacter ((r:K)*u)) *
      (∑ s : E, traceCharacter ((s:K)*v)) =
      if (∀ a ∈ E, Algebra.trace (ZMod 2) K (a*u)=0) ∧
         (∀ a ∈ E, Algebra.trace (ZMod 2) K (a*v)=0)
      then (Fintype.card E:ℝ)^2 else 0 := by
  rw [k4GeneralTrace_character_sum E u, k4GeneralTrace_character_sum E v]
  split_ifs <;> simp_all
  all_goals ring

theorem k4GeneralTrace_product_eq_double_sum
    (E : Submodule (ZMod 2) K) (u v : K) :
    (∑ r : E, traceCharacter ((r:K)*u)) *
      (∑ s : E, traceCharacter ((s:K)*v)) =
      ∑ r : E, ∑ s : E,
        traceCharacter ((r:K)*u+(s:K)*v) := by
  calc
    _ = ∑ r : E, traceCharacter ((r:K)*u) *
        (∑ s : E, traceCharacter ((s:K)*v)) := by rw [Finset.sum_mul]
    _ = ∑ r : E, ∑ s : E,
        traceCharacter ((r:K)*u+(s:K)*v) := by
      apply Fintype.sum_congr
      intro r
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro s
      rw [← AddChar.map_add_eq_mul]

theorem k4GeneralTrace_normOne_fourier_expansion
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (E : Submodule (ZMod 2) K) :
    (∑ p : k4NormOnePairs (K:=K),
      (∑ r : E, traceCharacter ((r:K)*p.val.2)) *
      (∑ s : E, traceCharacter ((s:K)*(p.val.1+p.val.2)))) =
      ∑ r : E, ∑ s : E,
        k4ASWFourierCoefficient (s:K) (r:K) := by
  calc
    _ = ∑ p : k4NormOnePairs (K:=K),
        ∑ r : E, ∑ s : E,
          traceCharacter ((r:K)*p.val.2+(s:K)*(p.val.1+p.val.2)) := by
      apply Fintype.sum_congr
      intro p
      exact k4GeneralTrace_product_eq_double_sum E p.val.2
        (p.val.1+p.val.2)
    _ = ∑ r : E, ∑ s : E, ∑ p : k4NormOnePairs (K:=K),
        traceCharacter ((r:K)*p.val.2+(s:K)*(p.val.1+p.val.2)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro r
      rw [Finset.sum_comm]
    _ = ∑ r : E, ∑ s : E,
        k4ASWFourierCoefficient (s:K) (r:K) := by
      apply Fintype.sum_congr
      intro r
      apply Fintype.sum_congr
      intro s
      exact k4NormOneFourier_sum_eq_coefficient n hn hfinrank (r:K) (s:K)

def k4GeneralTraceGood (E : Submodule (ZMod 2) K)
    (p : k4NormOnePairs (K:=K)) : Prop :=
  (∀ a ∈ E, Algebra.trace (ZMod 2) K (a*p.val.2)=0) ∧
  (∀ a ∈ E, Algebra.trace (ZMod 2) K (a*(p.val.1+p.val.2))=0)

noncomputable instance k4GeneralTraceGoodFintype (E : Submodule (ZMod 2) K) :
    Fintype {p : k4NormOnePairs (K:=K) // k4GeneralTraceGood E p} :=
  Fintype.ofFinite _

theorem k4GeneralTraceGood_card_filter (E : Submodule (ZMod 2) K) :
    (∑ p : k4NormOnePairs (K:=K),
      if k4GeneralTraceGood E p then (16:ℝ) else 0) =
      (Fintype.card {p : k4NormOnePairs (K:=K) // k4GeneralTraceGood E p}:ℝ)*16 := by
  classical
  let P : k4NormOnePairs (K:=K) → Prop := fun p => k4GeneralTraceGood E p
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

theorem k4GeneralTraceGood_card_fourier_sum
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (E : Submodule (ZMod 2) K) (hcard : Fintype.card E=4) :
    (Fintype.card {p : k4NormOnePairs (K:=K) // k4GeneralTraceGood E p}:ℝ)*16 =
      ∑ r : E, ∑ s : E,
        k4ASWFourierCoefficient (s:K) (r:K) := by
  calc
    _ = ∑ p : k4NormOnePairs (K:=K),
        if k4GeneralTraceGood E p then (16:ℝ) else 0 :=
      (k4GeneralTraceGood_card_filter E).symm
    _ = ∑ p : k4NormOnePairs (K:=K),
        (∑ r : E, traceCharacter ((r:K)*p.val.2)) *
        (∑ s : E, traceCharacter ((s:K)*(p.val.1+p.val.2))) := by
      apply Fintype.sum_congr
      intro p
      by_cases hg : k4GeneralTraceGood E p
      · have hc : (∀ a ∈ E, Algebra.trace (ZMod 2) K (a*p.val.2)=0) ∧
            (∀ a ∈ E, Algebra.trace (ZMod 2) K
              (a*(p.val.1+p.val.2))=0) := hg
        rw [if_pos hg, k4GeneralTrace_joint_filter E p.val.2
          (p.val.1+p.val.2), if_pos hc]
        norm_num [hcard]
      · have hc : ¬((∀ a ∈ E, Algebra.trace (ZMod 2) K (a*p.val.2)=0) ∧
            (∀ a ∈ E, Algebra.trace (ZMod 2) K
              (a*(p.val.1+p.val.2))=0)) := hg
        rw [if_neg hg, k4GeneralTrace_joint_filter E p.val.2
          (p.val.1+p.val.2), if_neg hc]
    _ = ∑ r : E, ∑ s : E,
        k4ASWFourierCoefficient (s:K) (r:K) :=
      k4GeneralTrace_normOne_fourier_expansion n hn hfinrank E

theorem k4GeneralTrace_fourier_sum_lower
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (E : Submodule (ZMod 2) K) (hcard : Fintype.card E=4) :
    (Fintype.card K:ℝ)+1-30*Real.sqrt (Fintype.card K:ℝ)-60 ≤
      ∑ r : E, ∑ s : E,
        k4ASWFourierCoefficient (s:K) (r:K) := by
  classical
  let α := E×E
  let f : α → ℝ := fun z => k4ASWFourierCoefficient (z.2:K) (z.1:K)
  let z : α := (⟨0,E.zero_mem⟩,⟨0,E.zero_mem⟩)
  have hcardα : Fintype.card α=16 := by simp [α,hcard]
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
      exact k4ASWFourierCoefficient_lower_of_hasse n hn hfinrank
        (x.2:K) (x.1:K) (Or.symm hpair)
    have hsum := Finset.sum_le_sum hpoint
    have herase : ((Finset.univ : Finset α).erase z).card=15 := by
      rw [Finset.card_erase_of_mem hzmem]
      simp [hcardα]
    calc
      (15:ℝ)*(-2*Real.sqrt (Fintype.card K:ℝ)-4) =
          ∑ x ∈ (Finset.univ : Finset α).erase z,
            (-2*Real.sqrt (Fintype.card K:ℝ)-4) := by
        simp [herase]
        ring
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).erase z, f x := hsum
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset α) f hzmem
  have htotal : ∑ x : α, f x =
      f z+∑ x ∈ (Finset.univ : Finset α).erase z, f x := by
    calc
      ∑ x : α, f x =
          (∑ x ∈ (Finset.univ : Finset α).erase z, f x)+f z := hsplit.symm
      _ = f z+∑ x ∈ (Finset.univ : Finset α).erase z, f x := by ring
  have hbound := add_le_add_left hrest (f z)
  rw [hzerof] at hbound
  have hfinal :
      (Fintype.card K:ℝ)+1-30*Real.sqrt (Fintype.card K:ℝ)-60 ≤
        ∑ x : α, f x := by
    rw [htotal]
    nlinarith
  simpa [α,f,Fintype.sum_prod_type] using hfinal

theorem k4GeneralTraceGood_card_gt_three
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (E : Submodule (ZMod 2) K) (hcard : Fintype.card E=4)
    (hq : 2048 ≤ Fintype.card K) :
    3 < Fintype.card
      {p : k4NormOnePairs (K:=K) // k4GeneralTraceGood E p} := by
  let N := Fintype.card
    {p : k4NormOnePairs (K:=K) // k4GeneralTraceGood E p}
  have hsum := k4GeneralTraceGood_card_fourier_sum n hn hfinrank E hcard
  have hlow := k4GeneralTrace_fourier_sum_lower n hn hfinrank E hcard
  have hN :
      ((Fintype.card K:ℝ)+1-30*Real.sqrt (Fintype.card K:ℝ)-60)/16 ≤
        (N:ℝ) := by
    rw [← hsum] at hlow
    dsimp [N]
    nlinarith
  exact k4_normOne_fourConstraint_count_gt_three_with_fiber_loss
    (Fintype.card K) N hq hN

#print axioms k4GeneralTrace_character_sum
#print axioms k4GeneralTraceGood_card_fourier_sum
#print axioms k4GeneralTrace_fourier_sum_lower
#print axioms k4GeneralTraceGood_card_gt_three

end Carlet
