import Carlet.K4ASWeierstrassFiberTraceProbe
import Carlet.K4NormOneCountArithmeticProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K]

attribute [local instance] Classical.propDecidable

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

local instance (E : Submodule (ZMod 2) K) : Fintype E := Fintype.ofFinite E

def k4NormOnePairs :=
  {p : K×K // p.1^2+p.1*p.2+p.2^2=1}

noncomputable instance k4NormOnePairsFintype : Fintype (k4NormOnePairs (K:=K)) := by
  classical
  unfold k4NormOnePairs
  exact Fintype.ofFinite _

def k4NormOneD (x : K) : K := x^2+x+1

noncomputable def k4NormOneParamPair (x : K) : K×K :=
  ((x^2+1)/k4NormOneD x,x^2/k4NormOneD x)

theorem k4NormOneParamPair_first_add_one
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (x : K) :
    (k4NormOneParamPair x).1+1=x/k4NormOneD x := by
  have hD := k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  have hD' : x^2+x+1≠0 := by simpa [k4ASD] using hD
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  dsimp [k4NormOneParamPair,k4NormOneD]
  have hnum : x^2+1+(x^2+x+1)=x := by
    calc
      x^2+1+(x^2+x+1)=x+(2:K)*(x^2+1) := by ring
      _=x := by rw [h2]; simp
  calc
    (x^2+1)/(x^2+x+1)+1=
        (x^2+1)/(x^2+x+1)+(x^2+x+1)/(x^2+x+1) := by
          rw [div_self hD']
    _=((x^2+1)+(x^2+x+1))/(x^2+x+1) := by rw [← add_div]
    _=x/(x^2+x+1) := by rw [hnum]

theorem k4NormOneParamPair_norm
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (x : K) :
    (k4NormOneParamPair x).1^2+
      (k4NormOneParamPair x).1*(k4NormOneParamPair x).2+
      (k4NormOneParamPair x).2^2=1 := by
  have hD : k4NormOneD x≠0 := by
    simpa [k4NormOneD,k4ASD] using
      (k4ASD_ne_zero_of_odd_finrank n hn hfinrank x)
  have hD' : x^2+x+1≠0 := by simpa [k4NormOneD] using hD
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have h3 : (3:K)=1 := by
    calc
      (3:K)=(2:K)+1 := by norm_num
      _=1 := by rw [h2]; simp
  have hDsq : (1+x^2+x^4)≠0 := by
    have hs : k4NormOneD x^2=1+x^2+x^4 := by
      dsimp [k4NormOneD]
      ring_nf
      simp [h2,h3]
    rw [← hs]
    exact pow_ne_zero 2 hD
  dsimp [k4NormOneParamPair,k4NormOneD]
  field_simp [hD']
  ring_nf
  simp [h2,h3]
  have hnum : x^2+x^4+1=1+x^2+x^4 := by ring
  calc
    _=(x^2+x^4+1)*(1+x^2+x^4)⁻¹ := by ring
    _=1 := by rw [hnum, mul_inv_cancel₀ hDsq]

theorem k4NormOneParamPair_second_add_first
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (x : K) :
    (k4NormOneParamPair x).1+(k4NormOneParamPair x).2=
      1/k4NormOneD x := by
  have hD : k4NormOneD x≠0 := by
    simpa [k4NormOneD,k4ASD] using
      (k4ASD_ne_zero_of_odd_finrank n hn hfinrank x)
  have hD' : x^2+x+1≠0 := by simpa [k4NormOneD] using hD
  dsimp [k4NormOneParamPair,k4NormOneD]
  field_simp [hD']
  have hnum : x^2+1+x^2=1 := by
    calc
      x^2+1+x^2=x^2+x^2+1 := by ring
      _=1 := by rw [CharTwo.add_self_eq_zero]; simp
  rw [hnum]

omit [Fintype K] in
theorem k4NormOne_param_denominator_mul
    {a u : K} (hnorm : a^2+a*u+u^2=1) (ha : a≠1) :
    k4NormOneD (u/(a+1))*(a+1)^2=u := by
  have hy : a+1≠0 := by
    intro h
    have ha1 : a=1 := by
      calc
        a=a+0 := by simp
        _=a+(1+1) := by rw [CharTwo.add_self_eq_zero]
        _=a+1+1 := by rw [← add_assoc]
        _=1 := by rw [h]; simp
    exact ha ha1
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  dsimp [k4NormOneD]
  field_simp [hy]
  ring_nf
  simp [h2]
  linear_combination hnorm + h2

omit [Fintype K] in
theorem k4NormOneParamPair_eq_of_norm_of_first_ne_one
    {a u : K} (hnorm : a^2+a*u+u^2=1) (ha : a≠1) :
    k4NormOneParamPair (u/(a+1))=(a,u) := by
  have hy : a+1≠0 := by
    intro h
    have ha1 : a=1 := by
      calc
        a=a+0 := by simp
        _=a+(1+1) := by rw [CharTwo.add_self_eq_zero]
        _=a+1+1 := by rw [← add_assoc]
        _=1 := by rw [h]; simp
    exact ha ha1
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have hpoly : u^2+u*(a+1)+(a+1)^2=u := by
    calc
      u^2+u*(a+1)+(a+1)^2=(a^2+a*u+u^2)+1+u := by
        ring_nf
        simp [h2]
      _=1+1+u := by rw [hnorm]
      _=u := by rw [CharTwo.add_self_eq_zero]; simp
  have hu : u≠0 := by
    intro hz
    have haSq : a^2=1 := by simpa [hz] using hnorm
    have hsquare : (a+1)^2=0 := by
      rw [add_sq]
      rw [h2, haSq]
      simp [CharTwo.add_self_eq_zero]
    have hmul : (a+1)*(a+1)=0 := by simpa [pow_two] using hsquare
    have hplus : a+1=0 := by
      rcases mul_eq_zero.mp hmul with hleft | hright
      · exact hleft
      · exact hright
    have ha1 : a=1 := by
      calc
        a=a+0 := by simp
        _=a+(1+1) := by rw [CharTwo.add_self_eq_zero]
        _=a+1+1 := by rw [← add_assoc]
        _=1 := by rw [hplus]; simp
    exact ha ha1
  have hdenNow : u*(u+(a+1))+(a+1)^2=u := by
    calc
      u*(u+(a+1))+(a+1)^2=
          u^2+u*(a+1)+(a+1)^2 := by ring
      _=u := hpoly
  have hnumFirst : u^2+(a+1)^2=a*u := by
    calc
      u^2+(a+1)^2=a^2+u^2+1 := by ring_nf; simp [h2]
      _=(a^2+a*u+u^2)+a*u+1 := by ring_nf; simp [h2]
      _=1+a*u+1 := by rw [hnorm]
      _=a*u := by
        calc
          1+a*u+1=(1+1)+a*u := by ring
          _=a*u := by rw [CharTwo.add_self_eq_zero]; simp
  apply Prod.ext
  · dsimp [k4NormOneParamPair,k4NormOneD]
    field_simp [hy]
    rw [hdenNow, hnumFirst]
    field_simp [hu]
  · dsimp [k4NormOneParamPair,k4NormOneD]
    field_simp [hy]
    rw [hdenNow]
    field_simp [hu]

noncomputable def k4NormOneParamOption : Option K → K×K
  | none => (1,1)
  | some x => k4NormOneParamPair x

omit [Fintype K] in
theorem k4NormOneParamOption_surjective_on_normOne
    {a u : K} (hnorm : a^2+a*u+u^2=1) :
    ∃ x : Option K, k4NormOneParamOption x=(a,u) := by
  by_cases ha : a=1
  · have hu_cases := k4_normOne_exceptions_of_first_eq_one a u hnorm ha
    rcases hu_cases with hu0 | hu1
    · refine ⟨some 0, ?_⟩
      subst a
      subst u
      simp [k4NormOneParamOption,k4NormOneParamPair,k4NormOneD]
    · refine ⟨none, ?_⟩
      subst a
      subst u
      simp [k4NormOneParamOption]
  · refine ⟨some (u/(a+1)), ?_⟩
    exact k4NormOneParamPair_eq_of_norm_of_first_ne_one hnorm ha

theorem k4NormOneParamOption_injective
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) :
    Function.Injective (k4NormOneParamOption (K:=K)) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      have hs := congrArg (fun p : K×K => p.1+p.2) hxy
      have hsum := k4NormOneParamPair_second_add_first n hn hfinrank y
      dsimp [k4NormOneParamOption] at hs
      rw [hsum, CharTwo.add_self_eq_zero] at hs
      have hD : k4NormOneD y≠0 := by
        simpa [k4NormOneD,k4ASD] using
          (k4ASD_ne_zero_of_odd_finrank n hn hfinrank y)
      have hone : (1:K)=0 := by
        have hs' : (0:K)=1/k4NormOneD y := by simpa using hs
        field_simp [hD] at hs'
        simpa using hs'.symm
      exact False.elim (one_ne_zero hone)
  | some x =>
    cases y with
    | none =>
      have hs := congrArg (fun p : K×K => p.1+p.2) hxy
      have hsum := k4NormOneParamPair_second_add_first n hn hfinrank x
      dsimp [k4NormOneParamOption] at hs
      rw [hsum, CharTwo.add_self_eq_zero] at hs
      have hD : k4NormOneD x≠0 := by
        simpa [k4NormOneD,k4ASD] using
          (k4ASD_ne_zero_of_odd_finrank n hn hfinrank x)
      have hzero : k4NormOneD x=0 := by simpa using hs
      exact False.elim (hD hzero)
    | some y =>
      have hratio := congrArg (fun p : K×K => p.1+1) hxy
      have hsum := congrArg (fun p : K×K => p.1+p.2) hxy
      have hxfirst := k4NormOneParamPair_first_add_one n hn hfinrank x
      have hyfirst := k4NormOneParamPair_first_add_one n hn hfinrank y
      have hxsum := k4NormOneParamPair_second_add_first n hn hfinrank x
      have hysum := k4NormOneParamPair_second_add_first n hn hfinrank y
      dsimp [k4NormOneParamOption] at hratio hsum
      rw [hxfirst, hyfirst] at hratio
      rw [hxsum, hysum] at hsum
      have hxD : k4NormOneD x≠0 := by
        simpa [k4NormOneD,k4ASD] using
          (k4ASD_ne_zero_of_odd_finrank n hn hfinrank x)
      have hyD : k4NormOneD y≠0 := by
        simpa [k4NormOneD,k4ASD] using
          (k4ASD_ne_zero_of_odd_finrank n hn hfinrank y)
      field_simp [hxD,hyD] at hratio hsum
      have hDxy : k4NormOneD x=k4NormOneD y := hsum.symm
      rw [hDxy] at hratio
      have hratio' : x*k4NormOneD y=y*k4NormOneD y := by
        simpa [mul_comm] using hratio
      have hxy' : x=y := mul_right_cancel₀ hyD hratio'
      exact congrArg some hxy'

noncomputable def k4NormOneParamSubtype
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (x : Option K) : k4NormOnePairs (K:=K) := by
  refine ⟨k4NormOneParamOption x, ?_⟩
  cases x with
  | none =>
    dsimp [k4NormOneParamOption]
    have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
    calc
      (1:K)^2+1*1+1^2=(2:K)+1 := by norm_num
      _=1 := by rw [h2]; simp
  | some x =>
    simpa [k4NormOneParamOption] using
      k4NormOneParamPair_norm n hn hfinrank x

noncomputable def k4NormOneParamEquiv
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) :
    Option K ≃ k4NormOnePairs (K:=K) :=
  Equiv.ofBijective (k4NormOneParamSubtype n hn hfinrank) ⟨by
    intro x y hxy
    apply k4NormOneParamOption_injective n hn hfinrank
    exact congrArg Subtype.val hxy, by
    intro p
    obtain ⟨x,hx⟩ := k4NormOneParamOption_surjective_on_normOne p.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx⟩

theorem k4NormOnePairs_card
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) :
    Fintype.card (k4NormOnePairs (K:=K))=Fintype.card K+1 := by
  calc
    Fintype.card (k4NormOnePairs (K:=K))=Fintype.card (Option K) :=
      Fintype.card_congr (k4NormOneParamEquiv n hn hfinrank).symm
    _=Fintype.card K+1 := by simp

theorem k4NormOneParamPair_character
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (r s x : K) :
    traceCharacter (r*(k4NormOneParamPair x).2+
      s*((k4NormOneParamPair x).1+(k4NormOneParamPair x).2))=
    traceCharacter (k4ASWFourierValue s r x) := by
  apply congrArg traceCharacter
  have hD : k4NormOneD x≠0 := by
    simpa [k4NormOneD,k4ASD] using
      k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  have hsum := k4NormOneParamPair_second_add_first n hn hfinrank x
  rw [hsum]
  dsimp [k4NormOneParamPair,k4NormOneD,k4ASWFourierValue,k4ASD]
  field_simp [hD]

theorem k4NormOneFourier_sum_eq_coefficient
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (r s : K) :
    (∑ p : k4NormOnePairs (K:=K),
      traceCharacter (r*p.val.2+s*(p.val.1+p.val.2)))=
      k4ASWFourierCoefficient s r := by
  classical
  let e := k4NormOneParamEquiv n hn hfinrank
  calc
    _ = ∑ x : Option K,
        traceCharacter (r*(k4NormOneParamSubtype n hn hfinrank x).val.2+
          s*((k4NormOneParamSubtype n hn hfinrank x).val.1+
            (k4NormOneParamSubtype n hn hfinrank x).val.2)) := by
      symm
      exact Equiv.sum_comp e
        (fun p : k4NormOnePairs (K:=K) =>
          traceCharacter (r*p.val.2+s*(p.val.1+p.val.2)))
    _ = traceCharacter r+
        ∑ x : K, traceCharacter (k4ASWFourierValue s r x) := by
      rw [Fintype.sum_option]
      simp only [k4NormOneParamSubtype, k4NormOneParamOption]
      have hfinite : ∀ x : K,
          traceCharacter (r*(k4NormOneParamPair x).2+
            s*((k4NormOneParamPair x).1+(k4NormOneParamPair x).2))=
          traceCharacter (k4ASWFourierValue s r x) := by
        intro x
        exact k4NormOneParamPair_character n hn hfinrank r s x
      have hinfty : traceCharacter (r*1+s*(1+1))=traceCharacter r := by
        congr 1
        rw [CharTwo.add_self_eq_zero]
        ring
      simp_rw [hfinite, hinfty]
    _ = k4ASWFourierCoefficient s r := by
      unfold k4ASWFourierCoefficient
      ring

def k4TracePlane (t : K) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) ({(1:K),t} : Set K)

def k4TracePlaneMulHom (t u : K) : k4TracePlane t →ₗ[ZMod 2] K where
  toFun r := (r:K)*u
  map_add' r s := by simp [add_mul]
  map_smul' c r := by simp [Algebra.smul_def, mul_assoc]

theorem k4TracePlane_character_sum
    (t u : K) :
    (∑ r : k4TracePlane t, traceCharacter ((r:K)*u)) =
      if ∀ a ∈ k4TracePlane t,
        Algebra.trace (ZMod 2) K (a*u)=0
      then (Nat.card (k4TracePlane t) : ℝ) else 0 := by
  classical
  let ψ : AddChar (k4TracePlane t) ℝ :=
    traceCharacter.compAddMonoidHom
      (k4TracePlaneMulHom t u).toAddMonoidHom
  have hzero : ψ=0 ↔ ∀ a ∈ k4TracePlane t,
      Algebra.trace (ZMod 2) K (a*u)=0 := by
    constructor
    · intro h a ha
      let r : k4TracePlane t := ⟨a,ha⟩
      have hh := congrArg (fun φ : AddChar (k4TracePlane t) ℝ => φ r) h
      change traceCharacter (a*u)=1 at hh
      exact (traceCharacter_eq_one_iff _).mp hh
    · intro h
      apply AddChar.ext
      intro r
      change traceCharacter ((r:K)*u)=1
      exact (traceCharacter_eq_one_iff _).mpr (h (r:K) r.property)
  have hs := AddChar.sum_eq_ite ψ
  change (∑ r : k4TracePlane t, ψ r) =
    if ψ=0 then (Fintype.card (k4TracePlane t) : ℝ) else 0 at hs
  by_cases hψ : ψ=0
  · have htrace := hzero.mp hψ
    simp only [if_pos hψ] at hs
    simp only [if_pos htrace]
    simpa [ψ, AddChar.compAddMonoidHom_apply,
      LinearMap.toAddMonoidHom_coe, k4TracePlaneMulHom,
      Submodule.coe_subtype, Nat.card_eq_fintype_card] using hs
  · have htrace : ¬ ∀ a ∈ k4TracePlane t,
        Algebra.trace (ZMod 2) K (a*u)=0 := fun h => hψ (hzero.mpr h)
    simp only [if_neg hψ] at hs
    simp only [if_neg htrace]
    simpa [ψ, AddChar.compAddMonoidHom_apply,
      LinearMap.toAddMonoidHom_coe, k4TracePlaneMulHom,
      Submodule.coe_subtype, Nat.card_eq_fintype_card] using hs

theorem k4TracePlane_joint_character_product
    (t u v : K) :
    (∑ r : k4TracePlane t, traceCharacter ((r:K)*u)) *
      (∑ s : k4TracePlane t, traceCharacter ((s:K)*v)) =
      if (∀ a ∈ k4TracePlane t,
          Algebra.trace (ZMod 2) K (a*u)=0) ∧
         (∀ a ∈ k4TracePlane t,
          Algebra.trace (ZMod 2) K (a*v)=0)
      then (Nat.card (k4TracePlane t) : ℝ)^2 else 0 := by
  rw [k4TracePlane_character_sum t u, k4TracePlane_character_sum t v]
  split_ifs <;> simp_all
  ring

theorem k4TracePlane_product_eq_double_sum
    (t u v : K) :
    (∑ r : k4TracePlane t, traceCharacter ((r:K)*u)) *
      (∑ s : k4TracePlane t, traceCharacter ((s:K)*v)) =
      ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        traceCharacter ((r:K)*u+(s:K)*v) := by
  calc
    _ = ∑ r : k4TracePlane t,
        traceCharacter ((r:K)*u) *
          (∑ s : k4TracePlane t, traceCharacter ((s:K)*v)) := by
      rw [Finset.sum_mul]
    _ = ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        traceCharacter ((r:K)*u+(s:K)*v) := by
      apply Fintype.sum_congr
      intro r
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro s
      rw [← AddChar.map_add_eq_mul]

theorem k4NormOne_joint_fourier_expansion
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n) (t : K) :
    (∑ p : k4NormOnePairs (K:=K),
      (∑ r : k4TracePlane t, traceCharacter ((r:K)*p.val.2)) *
      (∑ s : k4TracePlane t,
        traceCharacter ((s:K)*(p.val.1+p.val.2)))) =
      ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        k4ASWFourierCoefficient (s:K) (r:K) := by
  calc
    _ = ∑ p : k4NormOnePairs (K:=K),
        ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
          traceCharacter ((r:K)*p.val.2+(s:K)*(p.val.1+p.val.2)) := by
      apply Fintype.sum_congr
      intro p
      exact k4TracePlane_product_eq_double_sum t p.val.2
        (p.val.1+p.val.2)
    _ = ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        ∑ p : k4NormOnePairs (K:=K),
          traceCharacter ((r:K)*p.val.2+(s:K)*(p.val.1+p.val.2)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro r
      rw [Finset.sum_comm]
    _ = ∑ r : k4TracePlane t, ∑ s : k4TracePlane t,
        k4ASWFourierCoefficient (s:K) (r:K) := by
      apply Fintype.sum_congr
      intro r
      apply Fintype.sum_congr
      intro s
      exact k4NormOneFourier_sum_eq_coefficient n hn hfinrank (r:K) (s:K)

#print axioms k4NormOneParamPair_norm
#print axioms k4NormOneParamPair_first_add_one
#print axioms k4NormOne_param_denominator_mul
#print axioms k4NormOneParamPair_eq_of_norm_of_first_ne_one
#print axioms k4NormOneParamOption_surjective_on_normOne
#print axioms k4NormOneParamOption_injective
#print axioms k4NormOneParamEquiv
#print axioms k4NormOnePairs_card
#print axioms k4NormOneParamPair_character
#print axioms k4NormOneFourier_sum_eq_coefficient
#print axioms k4TracePlane_character_sum
#print axioms k4TracePlane_joint_character_product
#print axioms k4TracePlane_product_eq_double_sum
#print axioms k4NormOne_joint_fourier_expansion

end Carlet
