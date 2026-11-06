import Carlet.K4ASWeierstrassSourceCountProbe
import Carlet.ArtinSchreier
import Carlet.TraceDuality
import Mathlib.Tactic

set_option linter.style.haveILetI false

namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

noncomputable instance k4ASWNonzeroFintype :
    Fintype {x : K // x≠0} := by
  classical
  exact Fintype.ofFinite _

noncomputable def k4ASWArtinSchreierFiber (t : K) :=
  {δ : K // δ^2+δ=t}

noncomputable instance k4ASWArtinSchreierFiberFintype (t : K) :
    Fintype (k4ASWArtinSchreierFiber t) := by
  classical
  unfold k4ASWArtinSchreierFiber
  exact Fintype.ofFinite _

noncomputable def k4ASWSourceValue (A B x : K) : K :=
  ((A+B)*x^2+A*x)/k4ASD x

noncomputable def k4ASWFourierValue (A B x : K) : K :=
  (B*x^2+A)/k4ASD x

noncomputable def k4ASWFourierCoefficient (A B : K) : ℝ :=
  (∑ x : K, traceCharacter (k4ASWFourierValue A B x))+traceCharacter B

omit [Algebra (ZMod 2) K] in
theorem k4ASWSum_eq_zero_add_nonzero (f : K → ℝ) :
    (∑ x : K, f x)=f 0+
      ∑ x : {x : K // x≠0}, f x.val := by
  classical
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset K) f
    (Finset.mem_univ (0:K))
  have hsubtype :
      (∑ x : {x : K // x≠0}, f x.val)=
        ∑ x ∈ (Finset.univ : Finset K).erase 0, f x := by
    symm
    exact Finset.sum_subtype ((Finset.univ : Finset K).erase 0)
      (by intro x; simp [Finset.mem_erase]) f
  rw [← hsubtype] at hsplit
  linarith

theorem k4ASWSourceValue_shift_identity
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x : K) :
    k4ASWSourceValue A B x + A = k4ASWFourierValue A B x := by
  have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  dsimp [k4ASWSourceValue,k4ASWFourierValue]
  field_simp [hD]
  dsimp [k4ASD]
  ring_nf
  rw [h2]
  simp

omit [Fintype K] in
theorem traceCharacter_add_eq_of_trace_zero (x c : K)
    (hc : Algebra.trace (ZMod 2) K c=0) :
    traceCharacter (x+c)=traceCharacter x := by
  rw [AddChar.map_add_eq_mul, (traceCharacter_eq_one_iff c).mpr hc, mul_one]

theorem k4ASWFourierValue_eq_sourceValue_of_trace_A_zero
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x : K) (hA : Algebra.trace (ZMod 2) K A=0) :
    traceCharacter (k4ASWFourierValue A B x)=
      traceCharacter (k4ASWSourceValue A B x) := by
  rw [← k4ASWSourceValue_shift_identity n hn hfinrank A B x]
  exact traceCharacter_add_eq_of_trace_zero
    (k4ASWSourceValue A B x) A hA

theorem k4ASWFourierCoefficient_eq_source_of_trace_A_zero
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hA : Algebra.trace (ZMod 2) K A=0) :
    k4ASWFourierCoefficient A B=
      1+(∑ x : {x : K // x≠0},
        traceCharacter (k4ASWSourceValue A B x.val))+traceCharacter B := by
  classical
  have hzero : traceCharacter (k4ASWFourierValue A B 0)=1 := by
    have heval : k4ASWFourierValue A B 0=A := by
      simp [k4ASWFourierValue,k4ASD]
    rw [heval]
    exact (traceCharacter_eq_one_iff A).mpr hA
  have hsum :
      (∑ x : {x : K // x≠0}, traceCharacter (k4ASWFourierValue A B x.val))=
        ∑ x : {x : K // x≠0}, traceCharacter (k4ASWSourceValue A B x.val) := by
    apply Fintype.sum_congr
    intro x
    exact k4ASWFourierValue_eq_sourceValue_of_trace_A_zero
      n hn hfinrank A B x.val hA
  dsimp [k4ASWFourierCoefficient]
  rw [k4ASWSum_eq_zero_add_nonzero, hzero, hsum]

noncomputable def k4ASWNonzeroInvEquiv :
    {x : K // x≠0} ≃ {x : K // x≠0} where
  toFun x := ⟨x.val⁻¹, inv_ne_zero x.property⟩
  invFun x := ⟨x.val⁻¹, inv_ne_zero x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem k4ASWFourierCoefficient_eq_source_of_trace_A_one_B_zero
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hA : Algebra.trace (ZMod 2) K A≠0)
    (hB : Algebra.trace (ZMod 2) K B=0) :
    k4ASWFourierCoefficient A B=
      ∑ x : {x : K // x≠0},
        traceCharacter (k4ASWSourceValue B A x.val) := by
  classical
  have hAchar : traceCharacter A= -1 := by
    have hsign : traceCharacter A=1 ∨ traceCharacter A= -1 := by
      change (if Algebra.trace (ZMod 2) K A=0 then (1:ℝ) else -1)=1 ∨
        (if Algebra.trace (ZMod 2) K A=0 then (1:ℝ) else -1)= -1
      split_ifs <;> simp
    rcases hsign with h | h
    · exact (hA ((traceCharacter_eq_one_iff A).mp h)).elim
    · exact h
  have hBchar : traceCharacter B=1 :=
    (traceCharacter_eq_one_iff B).mpr hB
  have hzero : traceCharacter (k4ASWFourierValue A B 0)= -1 := by
    have heval : k4ASWFourierValue A B 0=A := by
      simp [k4ASWFourierValue,k4ASD]
    rw [heval]
    exact hAchar
  have hsum :
      (∑ x : {x : K // x≠0}, traceCharacter (k4ASWFourierValue A B x.val))=
        ∑ x : {x : K // x≠0}, traceCharacter (k4ASWSourceValue B A x.val) := by
    calc
      _ = ∑ x : {x : K // x≠0},
          traceCharacter (k4ASWFourierValue A B x.val⁻¹) := by
        symm
        exact Equiv.sum_comp (k4ASWNonzeroInvEquiv (K:=K))
          (fun x => traceCharacter (k4ASWFourierValue A B x.val))
      _ = _ := by
        apply Fintype.sum_congr
        intro x
        have hpoint : k4ASWFourierValue A B x.val⁻¹=
            k4ASWSourceValue B A x.val+B := by
          have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x.val
          have hDi := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x.val⁻¹
          have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
          dsimp [k4ASWFourierValue,k4ASWSourceValue]
          field_simp [hD,hDi,x.property]
          dsimp [k4ASD]
          field_simp [x.property]
          ring_nf
          have h3 : (3:K)=1 := by
            calc
              (3:K)=(2:K)+1 := by norm_num
              _=1 := by rw [h2]; simp
          have h4 : (4:K)=0 := by
            calc
              (4:K)=(2:K)*(2:K) := by norm_num
              _=0 := by rw [h2]; simp
          have h5 : (5:K)=1 := by
            calc
              (5:K)=(4:K)+1 := by norm_num
              _=1 := by rw [h4]; simp
          simp [h2,h3,h4,h5]
        rw [hpoint]
        exact traceCharacter_add_eq_of_trace_zero
          (k4ASWSourceValue B A x.val) B hB
  dsimp [k4ASWFourierCoefficient]
  rw [k4ASWSum_eq_zero_add_nonzero, hzero, hsum, hBchar]
  ring

theorem k4ASWFourierValue_inv_swap_identity
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x : K) (hx : x≠0) :
    k4ASWFourierValue A B x⁻¹ =
      k4ASWSourceValue B A x+B := by
  have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  have hDi := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x⁻¹
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  dsimp [k4ASWFourierValue,k4ASWSourceValue]
  field_simp [hD,hDi,hx]
  dsimp [k4ASD]
  field_simp [hx]
  ring_nf
  have h3 : (3:K)=1 := by
    calc
      (3:K)=(2:K)+1 := by norm_num
      _=1 := by rw [h2]; simp
  have h4 : (4:K)=0 := by
    calc
      (4:K)=(2:K)*(2:K) := by norm_num
      _=0 := by rw [h2]; simp
  have h5 : (5:K)=1 := by
    calc
      (5:K)=(4:K)+1 := by norm_num
      _=1 := by rw [h4]; simp
  simp [h2,h3,h4,h5]

theorem k4ASWFourierValue_inv_swap_trace
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x : K) (hx : x≠0)
    (hB : Algebra.trace (ZMod 2) K B=0) :
    traceCharacter (k4ASWFourierValue A B x⁻¹)=
      traceCharacter (k4ASWSourceValue B A x) := by
  rw [k4ASWFourierValue_inv_swap_identity n hn hfinrank A B x hx]
  exact traceCharacter_add_eq_of_trace_zero
    (k4ASWSourceValue B A x) B hB

omit [Fintype K] in
theorem k4ASW_denominator_translate (x : K) :
    k4ASD (x+1)=k4ASD x := by
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  dsimp [k4ASD]
  ring_nf
  have h3 : (3:K)=1 := by
    calc
      (3:K)=(2:K)+1 := by norm_num
      _=1 := by rw [h2]; simp
  rw [h3]
  ring

theorem k4ASWFourierValue_translate_identity
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x : K) :
    k4ASWFourierValue A B (x+1)=
      k4ASWSourceValue (A+B) B x+(A+B) := by
  have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  change (B*(x+1)^2+A)/k4ASD (x+1)=_
  rw [k4ASW_denominator_translate]
  dsimp [k4ASWFourierValue,k4ASWSourceValue]
  field_simp [hD]
  dsimp [k4ASD]
  ring_nf
  have h3 : (3:K)=1 := by
    calc
      (3:K)=(2:K)+1 := by norm_num
      _=1 := by rw [h2]; simp
  simp [h2,h3]

theorem k4ASWFourierValue_translate_trace
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x : K) (hAB : Algebra.trace (ZMod 2) K (A+B)=0) :
    traceCharacter (k4ASWFourierValue A B (x+1))=
      traceCharacter (k4ASWSourceValue (A+B) B x) := by
  rw [k4ASWFourierValue_translate_identity n hn hfinrank A B x]
  exact traceCharacter_add_eq_of_trace_zero
    (k4ASWSourceValue (A+B) B x) (A+B) hAB

theorem k4ASWFourierCoefficient_eq_source_of_both_traces_nonzero
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hA : Algebra.trace (ZMod 2) K A≠0)
    (hB : Algebra.trace (ZMod 2) K B≠0) :
    k4ASWFourierCoefficient A B=
      ∑ x : {x : K // x≠0},
        traceCharacter (k4ASWSourceValue (A+B) B x.val) := by
  classical
  have hsign (z : K) : traceCharacter z=1 ∨ traceCharacter z= -1 := by
    change (if Algebra.trace (ZMod 2) K z=0 then (1:ℝ) else -1)=1 ∨
      (if Algebra.trace (ZMod 2) K z=0 then (1:ℝ) else -1)= -1
    split_ifs <;> simp
  have hAchar : traceCharacter A= -1 := by
    rcases hsign A with h | h
    · exact (hA ((traceCharacter_eq_one_iff A).mp h)).elim
    · exact h
  have hBchar : traceCharacter B= -1 := by
    rcases hsign B with h | h
    · exact (hB ((traceCharacter_eq_one_iff B).mp h)).elim
    · exact h
  have hABchar : traceCharacter (A+B)=1 := by
    rw [AddChar.map_add_eq_mul, hAchar, hBchar]
    norm_num
  have hAB : Algebra.trace (ZMod 2) K (A+B)=0 :=
    (traceCharacter_eq_one_iff (A+B)).mp hABchar
  have hzero : traceCharacter (k4ASWSourceValue (A+B) B 0)=1 := by
    have heval : k4ASWSourceValue (A+B) B 0=0 := by
      simp [k4ASWSourceValue,k4ASD]
    rw [heval]
    simp [traceCharacter]
  have hsum :
      (∑ x : K, traceCharacter (k4ASWFourierValue A B x))=
        ∑ x : K, traceCharacter (k4ASWSourceValue (A+B) B x) := by
    calc
      _ = ∑ x : K,
          traceCharacter (k4ASWFourierValue A B (x+1)) := by
        symm
        exact Equiv.sum_comp (Equiv.addRight (1:K))
          (fun x => traceCharacter (k4ASWFourierValue A B x))
      _ = _ := by
        apply Fintype.sum_congr
        intro x
        exact k4ASWFourierValue_translate_trace n hn hfinrank A B x hAB
  dsimp [k4ASWFourierCoefficient]
  rw [hsum, k4ASWSum_eq_zero_add_nonzero, hzero, hBchar]
  ring

theorem k4ASWSourceRelation_iff (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B x δ : K) :
    k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x ↔
      δ^2+δ=k4ASWSourceValue A B x := by
  have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  constructor
  · intro h
    dsimp [k4ASWSourceValue]
    calc
      δ^2+δ = (k4ASD x*(δ^2+δ))/k4ASD x := by field_simp [hD]
      _ = ((A+B)*x^2+A*x)/k4ASD x := by rw [h]
  · intro h
    dsimp [k4ASWSourceValue] at h
    calc
      k4ASD x*(δ^2+δ) = k4ASD x*(((A+B)*x^2+A*x)/k4ASD x) := by rw [h]
      _ = (A+B)*x^2+A*x := by field_simp [hD]

noncomputable def k4ASWSourcePairsEquivSigma
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (A B : K) :
    k4ASWSourcePairs A B ≃
      Σ x : {x : K // x≠0},
        k4ASWArtinSchreierFiber (k4ASWSourceValue A B x.val) where
  toFun p :=
    ⟨⟨p.val.1,p.property.1⟩,
      ⟨p.val.2,(k4ASWSourceRelation_iff n hn hfinrank A B
        p.val.1 p.val.2).mp p.property.2⟩⟩
  invFun p :=
    ⟨(p.1.val,p.2.val),p.1.property,
      (k4ASWSourceRelation_iff n hn hfinrank A B
        p.1.val p.2.val).mpr p.2.property⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    cases p with
    | mk x y => rfl

theorem k4ASWSourcePairs_card_eq_fiber_sum
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (A B : K) :
    Fintype.card (k4ASWSourcePairs A B) =
      ∑ x : {x : K // x≠0},
        Fintype.card (k4ASWArtinSchreierFiber
          (k4ASWSourceValue A B x.val)) := by
  classical
  rw [Fintype.card_congr (k4ASWSourcePairsEquivSigma n hn hfinrank A B),
    Fintype.card_sigma]

theorem k4ASWArtinSchreierFiber_card (t : K) :
    Fintype.card (k4ASWArtinSchreierFiber t) =
      if Algebra.trace (ZMod 2) K t=0 then 2 else 0 := by
  classical
  by_cases htr : Algebra.trace (ZMod 2) K t=0
  · have hmem : t ∈ LinearMap.range (artinSchreier (K := K)) := by
      rw [artinSchreier_range]
      exact LinearMap.mem_ker.mpr htr
    obtain ⟨r,hr⟩ := hmem
    have hr' : r^2+r=t := by simpa [artinSchreier_apply] using hr
    have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
    have hr1 : (r+1)^2+(r+1)=t := by
      have heq : (r+1)^2+(r+1)=r^2+r := by
        ring_nf
        linear_combination (r+1)*h2
      exact heq.trans hr'
    have hdistinct : r≠r+1 := by
      intro h
      have hrr : r+r=0 := CharTwo.add_self_eq_zero r
      have hone : (1:K)=0 := by
        calc
          1=r+(r+1) := by
            calc
              1=1+(r+r) := by rw [hrr]; simp
              _=r+(r+1) := by ring
          _=r+r := by rw [← h]
          _=0 := hrr
      exact one_ne_zero hone
    let e : Bool → k4ASWArtinSchreierFiber t := fun b =>
      if b then ⟨r+1,hr1⟩ else ⟨r,hr'⟩
    have hinj : Function.Injective e := by
      intro b c h
      cases b <;> cases c
      · rfl
      · have hv := congrArg Subtype.val h
        exact (hdistinct hv).elim
      · have hv := congrArg Subtype.val h
        exact (hdistinct hv.symm).elim
      · rfl
    have hlower : 2 ≤ Fintype.card (k4ASWArtinSchreierFiber t) := by
      have h := Fintype.card_le_of_injective e hinj
      simpa using h
    have heval (δ : K) :
        δ^2+δ=t ↔ (k4ASWQuadratic t).eval δ=0 := by
      have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
      simp only [k4ASWQuadratic, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      constructor
      · intro h
        calc
          δ^2+δ+t=t+t := by rw [h]
          _=0 := CharTwo.add_self_eq_zero t
      · intro h
        have h' : δ^2+δ = -t := (eq_neg_iff_add_eq_zero).2 h
        simpa [CharTwo.neg_eq] using h'
    let eRoots : k4ASWArtinSchreierFiber t ≃
        {δ : K // (k4ASWQuadratic t).eval δ=0} :=
      Equiv.subtypeEquivProp (by
        funext δ
        exact propext (heval δ))
    have hupper : Fintype.card (k4ASWArtinSchreierFiber t) ≤ 2 := by
      calc
        _=Fintype.card {δ : K // (k4ASWQuadratic t).eval δ=0} :=
          Fintype.card_congr eRoots
        _≤2 := k4ASWQuadratic_roots_card_le_two t
    have hcard : Fintype.card (k4ASWArtinSchreierFiber t)=2 :=
      Nat.le_antisymm hupper hlower
    simpa [htr] using hcard
  · have hnotmem : t ∉ LinearMap.range (artinSchreier (K := K)) := by
      intro ht
      rw [artinSchreier_range] at ht
      exact htr (LinearMap.mem_ker.mp ht)
    have hempty : IsEmpty (k4ASWArtinSchreierFiber t) := by
      refine ⟨fun x => ?_⟩
      apply hnotmem
      refine ⟨x.val, ?_⟩
      simpa [artinSchreier_apply] using x.property
    letI : IsEmpty (k4ASWArtinSchreierFiber t) := hempty
    simp [htr]

theorem k4ASWArtinSchreierFiber_card_real (t : K) :
    (Fintype.card (k4ASWArtinSchreierFiber t) : ℝ)=
      1+traceCharacter t := by
  classical
  have hsign : traceCharacter t=1 ∨ traceCharacter t= -1 := by
    change (if Algebra.trace (ZMod 2) K t=0 then (1:ℝ) else -1)=1 ∨
      (if Algebra.trace (ZMod 2) K t=0 then (1:ℝ) else -1)= -1
    split_ifs <;> simp
  rcases hsign with hsign | hsign
  · have htr : Algebra.trace (ZMod 2) K t=0 :=
      (traceCharacter_eq_one_iff t).mp hsign
    norm_num [k4ASWArtinSchreierFiber_card, htr, hsign]
  · have htr : Algebra.trace (ZMod 2) K t≠0 := by
      intro h
      have hone := (traceCharacter_eq_one_iff t).mpr h
      rw [hsign] at hone
      norm_num at hone
    norm_num [k4ASWArtinSchreierFiber_card, htr, hsign]

theorem k4ASWSourcePairs_card_eq_trace_sum
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (A B : K) :
    (Fintype.card (k4ASWSourcePairs A B) : ℝ) =
      (Fintype.card {x : K // x≠0} : ℝ)+
        ∑ x : {x : K // x≠0},
          traceCharacter (k4ASWSourceValue A B x.val) := by
  classical
  rw [k4ASWSourcePairs_card_eq_fiber_sum n hn hfinrank A B]
  rw [Nat.cast_sum]
  calc
    (∑ x : {x : K // x≠0},
      (Fintype.card (k4ASWArtinSchreierFiber
        (k4ASWSourceValue A B x.val)) : ℝ))
        = ∑ x : {x : K // x≠0},
          (1+traceCharacter (k4ASWSourceValue A B x.val)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact k4ASWArtinSchreierFiber_card_real _
    _ = (Fintype.card {x : K // x≠0} : ℝ)+
        ∑ x : {x : K // x≠0},
          traceCharacter (k4ASWSourceValue A B x.val) := by
          simp [Finset.sum_add_distrib]

omit [Algebra (ZMod 2) K] in
theorem k4ASWNonzero_card_add_one :
    Fintype.card {x : K // x≠0}+1=Fintype.card K := by
  classical
  have hfilter :
      (Finset.univ.filter (fun x : K => x≠0))=(Finset.univ.erase 0) := by
    ext x
    simp [Finset.mem_erase]
  rw [Fintype.card_subtype]
  rw [hfilter]
  simpa using Finset.card_erase_add_one (Finset.mem_univ (0:K))

theorem k4ASWSourceTraceSum_lower_of_hasse
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hnorm : A^2+A*B+B^2 ≠ 0) :
    -2*Real.sqrt (Fintype.card K : ℝ)-4 ≤
      ∑ x : {x : K // x≠0},
        traceCharacter (k4ASWSourceValue A B x.val) := by
  have hsource := k4ASWSourcePairs_card_lower_of_hasse
    n hn hfinrank A B hnorm
  rw [k4ASWSourcePairs_card_eq_trace_sum n hn hfinrank A B] at hsource
  have hnonzero := k4ASWNonzero_card_add_one (K:=K)
  have hnonzeroR :
      (Fintype.card {x : K // x≠0} : ℝ)+1=(Fintype.card K : ℝ) := by
    exact_mod_cast hnonzero
  linarith

theorem k4ASW_discriminant_ne_zero_of_odd_finrank
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hAB : A≠0 ∨ B≠0) :
    A^2+A*B+B^2 ≠ 0 := by
  intro hnorm
  by_cases hB : B=0
  · have hA : A≠0 := by
      intro hA
      rcases hAB with hA' | hB'
      · exact hA' hA
      · exact hB' hB
    subst B
    have hA2 : A^2=0 := by simpa using hnorm
    exact (pow_ne_zero 2 hA) hA2
  · have hratio : (A/B)^2+(A/B)+1=0 := by
      field_simp [hB]
      linear_combination hnorm
    have hD : k4ASD (A/B)=0 := by
      simp [k4ASD,hratio]
    exact (k4ASD_ne_zero_of_odd_finrank n hn hfinrank (A/B)) hD

theorem k4ASWFourierCoefficient_lower_of_hasse
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hAB : A≠0 ∨ B≠0) :
    -2*Real.sqrt (Fintype.card K : ℝ)-4 ≤
      k4ASWFourierCoefficient A B := by
  classical
  by_cases hA0 : Algebra.trace (ZMod 2) K A=0
  · have hdisc := k4ASW_discriminant_ne_zero_of_odd_finrank
      n hn hfinrank A B hAB
    have hT := k4ASWSourceTraceSum_lower_of_hasse
      n hn hfinrank A B hdisc
    have hsignB : traceCharacter B=1 ∨ traceCharacter B= -1 := by
      change (if Algebra.trace (ZMod 2) K B=0 then (1:ℝ) else -1)=1 ∨
        (if Algebra.trace (ZMod 2) K B=0 then (1:ℝ) else -1)= -1
      split_ifs <;> simp
    have hcorrection : 0≤1+traceCharacter B := by
      rcases hsignB with h | h <;> rw [h] <;> norm_num
    rw [k4ASWFourierCoefficient_eq_source_of_trace_A_zero
      n hn hfinrank A B hA0]
    linarith
  · by_cases hB0 : Algebra.trace (ZMod 2) K B=0
    · have hdisc := k4ASW_discriminant_ne_zero_of_odd_finrank
        n hn hfinrank B A (Or.symm hAB)
      have hT := k4ASWSourceTraceSum_lower_of_hasse
        n hn hfinrank B A hdisc
      rw [k4ASWFourierCoefficient_eq_source_of_trace_A_one_B_zero
        n hn hfinrank A B hA0 hB0]
      exact hT
    · have hC : A+B≠0 ∨ B≠0 := by
        by_cases hB : B=0
        · left
          have hBn : ¬ B≠0 := by simp [hB]
          have hA := hAB.resolve_right hBn
          simpa [hB] using hA
        · exact Or.inr hB
      have hdisc := k4ASW_discriminant_ne_zero_of_odd_finrank
        n hn hfinrank (A+B) B hC
      have hT := k4ASWSourceTraceSum_lower_of_hasse
        n hn hfinrank (A+B) B hdisc
      rw [k4ASWFourierCoefficient_eq_source_of_both_traces_nonzero
        n hn hfinrank A B hA0 hB0]
      exact hT

omit [Fintype K] in
theorem k4ASW_source_exceptional_X_polynomial
    (A B x δ : K) (hx : x≠0)
    (hcurve : k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x)
    (hX : k4ASWeierstrassX A x δ=A^2+B) :
    x^3*((A^2+B)^2*x+A^2)=0 := by
  let C := A^2+B
  let D := x^2+x+1
  let M := C*x^2+A*x*(x+1)
  let N := (A+B)*x^2+A*x
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have hNX : k4ASNX A x δ=C*x^2 := by
    dsimp [k4ASWeierstrassX] at hX
    field_simp [hx] at hX
    simpa [C, mul_comm] using hX
  have hM : D*δ=M := by
    dsimp [M,D,C,k4ASNX,k4ASD] at hNX ⊢
    ring_nf at hNX ⊢
    simp [h2] at hNX ⊢
    linear_combination hNX-(A*x+A*x^2)*h2
  have hcurve0 : D*(δ^2+δ)+N=0 := by
    dsimp [D,N,k4ASD] at hcurve ⊢
    linear_combination hcurve+N*h2
  have hpoly : M^2+M*D+N*D=0 := by
    rw [← hM]
    calc
      (D*δ)^2+(D*δ)*D+N*D = D*(D*(δ^2+δ)+N) := by ring
      _ = 0 := by rw [hcurve0]; simp
  have hid : M^2+M*D+N*D=x^3*(C^2*x+A^2) := by
    dsimp [M,D,N,C]
    have h3 : (3:K)=1 := by
      calc
        (3:K)=(2:K)+1 := by norm_num
        _=1 := by rw [h2]; simp
    have h4 : (4:K)=0 := by
      calc
        (4:K)=(2:K)*(2:K) := by norm_num
        _=0 := by rw [h2]; simp
    ring_nf
    simp [h2,h3,h4]
  rw [hid] at hpoly
  exact hpoly

noncomputable def k4ASWExceptionalSourcePairs (A B : K) :=
  {s : k4ASWSourcePairs A B //
    k4ASWeierstrassX A s.val.1 s.val.2=A^2+B}

noncomputable instance k4ASWExceptionalSourcePairsFintype (A B : K) :
    Fintype (k4ASWExceptionalSourcePairs A B) := by
  classical
  unfold k4ASWExceptionalSourcePairs
  exact Fintype.ofFinite _

theorem k4ASWExceptionalSourcePairs_subsingleton
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hnorm : A^2+A*B+B^2≠0) :
    Subsingleton (k4ASWExceptionalSourcePairs A B) := by
  classical
  refine ⟨?_⟩
  intro p q
  have hp := k4ASW_source_exceptional_X_polynomial A B
    p.val.val.1 p.val.val.2 p.val.property.1 p.val.property.2 p.property
  have hq := k4ASW_source_exceptional_X_polynomial A B
    q.val.val.1 q.val.val.2 q.val.property.1 q.val.property.2 q.property
  have hC : A^2+B≠0 := by
    by_contra hC
    have hA2 : A^2=0 := by
      have hp' := mul_eq_zero.mp hp
      rcases hp' with hp' | hp'
      · have : p.val.val.1^3=0 := hp'
        exact (p.val.property.1 (eq_zero_of_pow_eq_zero this)).elim
      · simpa [hC] using hp'
    have hA : A=0 := eq_zero_of_pow_eq_zero hA2
    have hB : B=0 := by
      have hC0 : A^2+B=0 := by simpa using hC
      simpa [hA] using hC0
    exact hnorm (by simp [hA,hB])
  have hpPoly := mul_eq_zero.mp hp
  have hpx : (A^2+B)^2*p.val.val.1+A^2=0 := by
    rcases hpPoly with hzero | hzero
    · exact (p.val.property.1 (eq_zero_of_pow_eq_zero hzero)).elim
    · exact hzero
  have hqPoly := mul_eq_zero.mp hq
  have hqx : (A^2+B)^2*q.val.val.1+A^2=0 := by
    rcases hqPoly with hzero | hzero
    · exact (q.val.property.1 (eq_zero_of_pow_eq_zero hzero)).elim
    · exact hzero
  have hx : p.val.val.1=q.val.val.1 := by
    have hpEq : (A^2+B)^2*p.val.val.1 = -A^2 :=
      (eq_neg_iff_add_eq_zero).2 hpx
    have hqEq : (A^2+B)^2*q.val.val.1 = -A^2 :=
      (eq_neg_iff_add_eq_zero).2 hqx
    have hmul : (A^2+B)^2*p.val.val.1=(A^2+B)^2*q.val.val.1 :=
      hpEq.trans hqEq.symm
    exact mul_left_cancel₀ (pow_ne_zero 2 hC) hmul
  have hNXp : k4ASNX A p.val.val.1 p.val.val.2=(A^2+B)*p.val.val.1^2 := by
    have hXp := p.property
    dsimp [k4ASWeierstrassX] at hXp
    field_simp [p.val.property.1] at hXp
    simpa [mul_comm] using hXp
  have hNXq : k4ASNX A q.val.val.1 q.val.val.2=(A^2+B)*q.val.val.1^2 := by
    have hXq := q.property
    dsimp [k4ASWeierstrassX] at hXq
    field_simp [q.val.property.1] at hXq
    simpa [mul_comm] using hXq
  have hNXq' : k4ASNX A p.val.val.1 q.val.val.2=
      (A^2+B)*p.val.val.1^2 := by
    simpa [hx] using hNXq
  have hNX : k4ASNX A p.val.val.1 p.val.val.2=
      k4ASNX A p.val.val.1 q.val.val.2 := by
    calc
      _=(A^2+B)*p.val.val.1^2 := hNXp
      _=(A^2+B)*q.val.val.1^2 := by rw [hx]
      _=_ := by
        calc
          _=(A^2+B)*p.val.val.1^2 := by rw [← hx]
          _=_ := hNXq'.symm
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have hδ : p.val.val.2=q.val.val.2 := by
    have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank p.val.val.1
    have hlinear : k4ASD p.val.val.1*(p.val.val.2+A*p.val.val.1)=
        k4ASD p.val.val.1*(q.val.val.2+A*p.val.val.1) := by
      have hNX' := hNX
      dsimp [k4ASNX,k4ASD] at hNX'
      have hsum := add_right_cancel hNX'
      simpa [k4ASD,k4ASNX] using hsum
    have hcancel := mul_left_cancel₀ hD hlinear
    exact add_right_cancel hcancel
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hx hδ

theorem k4ASWExceptionalSourcePairs_card_le_one
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hnorm : A^2+A*B+B^2≠0) :
    Fintype.card (k4ASWExceptionalSourcePairs A B)≤1 := by
  have h := k4ASWExceptionalSourcePairs_subsingleton n hn hfinrank A B hnorm
  exact Fintype.card_le_one_iff_subsingleton.mpr h

noncomputable def k4ASWGenericSourcePairs (A B : K) :=
  {s : k4ASWSourcePairs A B //
    k4ASWeierstrassX A s.val.1 s.val.2+k4ASC A B≠0}

noncomputable instance k4ASWGenericSourcePairsFintype (A B : K) :
    Fintype (k4ASWGenericSourcePairs A B) := by
  classical
  unfold k4ASWGenericSourcePairs
  exact Fintype.ofFinite _

noncomputable def k4ASWSourceToWeierstrassPair (A B : K)
    (s : k4ASWSourcePairs A B) : k4ASWeierstrassPairs A B :=
  k4ASAffinePointToWeierstrassPair A B s.val.1 s.val.2
    s.property.1 s.property.2

theorem k4ASWSourceToWeierstrassPair_injective_generic
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) :
    Function.Injective (fun s : k4ASWGenericSourcePairs A B =>
      k4ASWSourceToWeierstrassPair A B s.val) := by
  intro p q hpq
  have hpair :
      (k4ASWSourceToWeierstrassPair A B p.val).val=
      (k4ASWSourceToWeierstrassPair A B q.val).val :=
    congrArg (fun w : k4ASWeierstrassPairs A B => w.val) hpq
  have hX : k4ASWeierstrassX A p.val.val.1 p.val.val.2=
      k4ASWeierstrassX A q.val.val.1 q.val.val.2 := by
    exact congrArg Prod.fst hpair
  have hY : k4ASWeierstrassY A B p.val.val.1 p.val.val.2=
      k4ASWeierstrassY A B q.val.val.1 q.val.val.2 := by
    exact congrArg Prod.snd hpair
  have hcoordp := k4ASWeierstrass_coordinate_relation A
    B p.val.val.1 p.val.val.2 p.val.property.1
  have hcoordq := k4ASWeierstrass_coordinate_relation A
    B q.val.val.1 q.val.val.2 q.val.property.1
  have hTp : k4ASWeierstrassY A B p.val.val.1 p.val.val.2+A+
      k4ASC A B≠0 := by
    intro ht
    apply p.property
    calc
      k4ASWeierstrassX A p.val.val.1 p.val.val.2+k4ASC A B=
          p.val.val.1*(k4ASWeierstrassY A B p.val.val.1 p.val.val.2+
            A+k4ASC A B) := hcoordp
      _=0 := by rw [ht]; simp
  have hTq : k4ASWeierstrassY A B q.val.val.1 q.val.val.2+A+
      k4ASC A B≠0 := by
    intro ht
    apply q.property
    calc
      k4ASWeierstrassX A q.val.val.1 q.val.val.2+k4ASC A B=
          q.val.val.1*(k4ASWeierstrassY A B q.val.val.1 q.val.val.2+
            A+k4ASC A B) := hcoordq
      _=0 := by rw [ht]; simp
  have hratioP : p.val.val.1=
      (k4ASWeierstrassX A p.val.val.1 p.val.val.2+k4ASC A B)/
        (k4ASWeierstrassY A B p.val.val.1 p.val.val.2+A+k4ASC A B) := by
    calc
      p.val.val.1=p.val.val.1*(k4ASWeierstrassY A B p.val.val.1 p.val.val.2+
          A+k4ASC A B)/(k4ASWeierstrassY A B p.val.val.1 p.val.val.2+
          A+k4ASC A B) := by field_simp [hTp]
      _=_ := by rw [hcoordp]
  have hratioQ : q.val.val.1=
      (k4ASWeierstrassX A q.val.val.1 q.val.val.2+k4ASC A B)/
        (k4ASWeierstrassY A B q.val.val.1 q.val.val.2+A+k4ASC A B) := by
    calc
      q.val.val.1=q.val.val.1*(k4ASWeierstrassY A B q.val.val.1 q.val.val.2+
          A+k4ASC A B)/(k4ASWeierstrassY A B q.val.val.1 q.val.val.2+
          A+k4ASC A B) := by field_simp [hTq]
      _=_ := by rw [hcoordq]
  have hx : p.val.val.1=q.val.val.1 := by
    rw [hratioP,hratioQ,hX,hY]
  have hNXp : k4ASNX A p.val.val.1 p.val.val.2=
      k4ASWeierstrassX A p.val.val.1 p.val.val.2*p.val.val.1^2 := by
    dsimp [k4ASWeierstrassX]
    field_simp [p.val.property.1]
  have hNXq : k4ASNX A q.val.val.1 q.val.val.2=
      k4ASWeierstrassX A q.val.val.1 q.val.val.2*q.val.val.1^2 := by
    dsimp [k4ASWeierstrassX]
    field_simp [q.val.property.1]
  rw [← hx] at hNXq
  have hNX : k4ASNX A p.val.val.1 p.val.val.2=
      k4ASNX A p.val.val.1 q.val.val.2 := by
    calc
      _=k4ASWeierstrassX A p.val.val.1 p.val.val.2*p.val.val.1^2 := hNXp
      _=k4ASWeierstrassX A q.val.val.1 q.val.val.2*q.val.val.1^2 := by rw [hX,hx]
      _=_ := by rw [← hx]; exact hNXq.symm
  have hδ : p.val.val.2=q.val.val.2 := by
    have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank p.val.val.1
    have hlinear : k4ASD p.val.val.1*(p.val.val.2+A*p.val.val.1)=
        k4ASD p.val.val.1*(q.val.val.2+A*p.val.val.1) := by
      have hNX' := hNX
      dsimp [k4ASNX,k4ASD] at hNX'
      have hsum := add_right_cancel hNX'
      simpa [k4ASD,k4ASNX] using hsum
    have hcancel := mul_left_cancel₀ hD hlinear
    exact add_right_cancel hcancel
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hx hδ

omit [Fintype K] in
theorem k4AS_add_eq_zero_iff_eq (x c : K) : x+c=0 ↔ x=c := by
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    calc
      x=x+0 := by simp
      _=x+(c+c) := by rw [CharTwo.add_self_eq_zero]
      _=(x+c)+c := by ac_rfl
      _=0+c := by rw [h]
      _=c := by simp
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero c

noncomputable def k4ASWSourcePartitionEquiv (A B : K) :
    k4ASWSourcePairs A B ≃
      Sum (k4ASWGenericSourcePairs A B) (k4ASWExceptionalSourcePairs A B) where
  toFun s := by
    classical
    by_cases h : k4ASWeierstrassX A s.val.1 s.val.2+k4ASC A B≠0
    · exact Sum.inl ⟨s,h⟩
    · have hz : k4ASWeierstrassX A s.val.1 s.val.2+k4ASC A B=0 :=
        Classical.not_not.mp h
      have heq := (k4AS_add_eq_zero_iff_eq
        (k4ASWeierstrassX A s.val.1 s.val.2) (k4ASC A B)).mp hz
      exact Sum.inr ⟨s, by simpa [k4ASC] using heq⟩
  invFun
    | Sum.inl s => s.val
    | Sum.inr s => s.val
  left_inv s := by
    classical
    dsimp
    split_ifs <;> rfl
  right_inv s := by
    classical
    cases s with
    | inl s =>
        change (if h : k4ASWeierstrassX A s.val.val.1 s.val.val.2+
            k4ASC A B≠0 then Sum.inl ⟨s.val,h⟩ else _) = Sum.inl s
        rw [dif_pos s.property]
        congr 1
    | inr s =>
        have hz : k4ASWeierstrassX A s.val.val.1 s.val.val.2+
            k4ASC A B=0 :=
          (k4AS_add_eq_zero_iff_eq _ _).mpr (by simpa [k4ASC] using s.property)
        change (if h : k4ASWeierstrassX A s.val.val.1 s.val.val.2+
            k4ASC A B≠0 then _ else Sum.inr ⟨s.val,s.property⟩) = Sum.inr s
        rw [dif_neg (by intro h; exact h hz)]
        congr 1

theorem k4ASWSourcePairs_card_le_weierstrass_add_one
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hnorm : A^2+A*B+B^2≠0) :
    Fintype.card (k4ASWSourcePairs A B) ≤
      Fintype.card (k4ASWeierstrassPairs A B)+1 := by
  classical
  rw [Fintype.card_congr (k4ASWSourcePartitionEquiv A B), Fintype.card_sum]
  have hgeneric : Fintype.card (k4ASWGenericSourcePairs A B) ≤
      Fintype.card (k4ASWeierstrassPairs A B) :=
    Fintype.card_le_of_injective
      (fun s => k4ASWSourceToWeierstrassPair A B s.val)
      (k4ASWSourceToWeierstrassPair_injective_generic n hn hfinrank A B)
  have hex : Fintype.card (k4ASWExceptionalSourcePairs A B)≤1 :=
    k4ASWExceptionalSourcePairs_card_le_one n hn hfinrank A B hnorm
  omega

theorem k4ASWSourceTraceSum_upper_of_hasse
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (hnorm : A^2+A*B+B^2≠0) :
    ∑ x : {x : K // x≠0},
      traceCharacter (k4ASWSourceValue A B x.val) ≤
        2*Real.sqrt (Fintype.card K : ℝ)+2 := by
  classical
  letI := k4ASWeierstrassPointFintype A B hnorm
  have hcount := k4ASWeierstrassCurve_pointCount A B hnorm
  have hhasse := k4ASWeierstrassCurve_hasse A B hnorm
  have hsource := k4ASWSourcePairs_card_le_weierstrass_add_one
    n hn hfinrank A B hnorm
  have hwupper :
      (Fintype.card (k4ASWeierstrassPairs A B) : ℝ) ≤
        (Fintype.card K : ℝ)+2*Real.sqrt (Fintype.card K : ℝ) := by
    rw [abs_le] at hhasse
    have hright := hhasse.2
    rw [hcount] at hright
    norm_num at hright ⊢
    linarith
  have hsourceR :
      (Fintype.card (k4ASWSourcePairs A B) : ℝ) ≤
        (Fintype.card (k4ASWeierstrassPairs A B) : ℝ)+1 := by
    exact_mod_cast hsource
  have hsourceR' :
      (Fintype.card (k4ASWSourcePairs A B) : ℝ) ≤
        (Fintype.card K : ℝ)+2*Real.sqrt (Fintype.card K : ℝ)+1 :=
    hsourceR.trans (by linarith)
  rw [k4ASWSourcePairs_card_eq_trace_sum n hn hfinrank A B] at hsourceR'
  have hnonzero := k4ASWNonzero_card_add_one (K:=K)
  have hnonzeroR :
      (Fintype.card {x : K // x≠0} : ℝ)+1=(Fintype.card K : ℝ) := by
    exact_mod_cast hnonzero
  linarith

#print axioms k4ASWArtinSchreierFiber_card
#print axioms k4ASWSourceValue_shift_identity
#print axioms k4ASWFourierCoefficient_eq_source_of_trace_A_zero
#print axioms k4ASWFourierCoefficient_eq_source_of_trace_A_one_B_zero
#print axioms k4ASWFourierValue_eq_sourceValue_of_trace_A_zero
#print axioms k4ASWFourierValue_inv_swap_identity
#print axioms k4ASWFourierValue_inv_swap_trace
#print axioms k4ASW_denominator_translate
#print axioms k4ASWFourierValue_translate_trace
#print axioms k4ASWFourierCoefficient_eq_source_of_both_traces_nonzero
#print axioms k4ASWArtinSchreierFiber_card_real
#print axioms k4ASWSourcePairs_card_eq_trace_sum
#print axioms k4ASWSourceTraceSum_lower_of_hasse
#print axioms k4ASW_discriminant_ne_zero_of_odd_finrank
#print axioms k4ASW_source_exceptional_X_polynomial
#print axioms k4ASWExceptionalSourcePairs_card_le_one
#print axioms k4ASWSourceToWeierstrassPair_injective_generic
#print axioms k4ASWSourcePairs_card_le_weierstrass_add_one
#print axioms k4ASWSourceTraceSum_upper_of_hasse
#print axioms k4ASWFourierCoefficient_lower_of_hasse

end Carlet
