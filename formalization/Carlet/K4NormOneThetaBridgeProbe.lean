import Carlet.K4GeneralTraceCountProbe
import Carlet.K4TracePlaneCardProbe
import Carlet.K4ThetaAsThreeSpaceImageProbe
import Carlet.K4ParametricExtensionProbe
import Carlet.TraceDuality
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
local instance k4ThetaBridgeFintype (E : Submodule (ZMod 2) K) :
    Fintype E := Fintype.ofFinite E

def k4ScalarMulMap (c : K) : K →ₗ[ZMod 2] K where
  toFun x := c*x
  map_add' x y := by simp [mul_add]
  map_smul' a x := by simp [Algebra.smul_def, mul_left_comm]

def k4ScaledSubspacePolynomialMap (E : Submodule (ZMod 2) K)
    (c : K) : K →ₗ[ZMod 2] K :=
  (k4ScalarMulMap c).comp (subspacePolynomialMap E)

theorem k4ScaledSubspacePolynomialMap_ker
    (E : Submodule (ZMod 2) K) (c : K) (hc : c≠0) :
    LinearMap.ker (k4ScaledSubspacePolynomialMap E c)=E := by
  ext x
  change c*(rootProduct (underlyingFinset E)).eval x=0 ↔ x∈E
  rw [mul_eq_zero, subspacePolynomial_eval_eq_zero_iff]
  simp [hc]

def k4NormOneThetaTracePlane (t : K) : Submodule (ZMod 2) K :=
  traceOrthogonal (LinearMap.range
    (k4ScaledSubspacePolynomialMap (k4TracePlane t) ((t^2+t+1)⁻¹^2)))

theorem k4NormOneThetaTracePlane_finrank
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    Module.finrank (ZMod 2) (k4NormOneThetaTracePlane t)=2 := by
  have hc : t^2+t+1≠0 := by
    simpa [k4ASD] using k4ASD_ne_zero_of_odd_finrank n hn hfinrank t
  have hscale : (t^2+t+1)⁻¹^2≠0 := by
    exact pow_ne_zero _ (inv_ne_zero hc)
  let H := k4TracePlane t
  have hHcard : Fintype.card H=4 := by
    simpa [H] using k4TracePlane_card_eq_four t ht0 ht1
  have hHpow : Fintype.card H=2^Module.finrank (ZMod 2) H := by
    have h := Module.card_eq_pow_finrank (K:=ZMod 2) (V:=H)
    simpa [Nat.card_eq_fintype_card, ZMod.card] using h
  have hHdim : Module.finrank (ZMod 2) H=2 := by
    have hh : 2^Module.finrank (ZMod 2) H=2^2 := by
      calc
        2^Module.finrank (ZMod 2) H=Fintype.card H := hHpow.symm
        _=4 := hHcard
        _=2^2 := by norm_num
    exact (Nat.pow_right_injective (by norm_num : 1<2)) hh
  let g := k4ScaledSubspacePolynomialMap H ((t^2+t+1)⁻¹^2)
  have hker : LinearMap.ker g=H := by
    simpa [g,H] using k4ScaledSubspacePolynomialMap_ker H _ hscale
  have hrange := LinearMap.finrank_range_add_finrank_ker g
  rw [hker,hHdim] at hrange
  have hS : Module.finrank (ZMod 2) (LinearMap.range g)=n-2 := by omega
  change Module.finrank (ZMod 2) (traceOrthogonal (LinearMap.range g))=2
  rw [traceOrthogonal_finrank,hS,hfinrank]
  omega

theorem k4NormOneThetaTracePlane_card
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1) :
    Fintype.card (k4NormOneThetaTracePlane t)=4 := by
  have hdim := k4NormOneThetaTracePlane_finrank n hn hfinrank t ht0 ht1
  have hpow : Fintype.card (k4NormOneThetaTracePlane t) =
      2^Module.finrank (ZMod 2) (k4NormOneThetaTracePlane t) := by
    have h := Module.card_eq_pow_finrank (K:=ZMod 2)
      (V:=k4NormOneThetaTracePlane t)
    simpa [Nat.card_eq_fintype_card,ZMod.card] using h
  rw [hdim] at hpow
  exact hpow

theorem k4NormOneThetaTracePlane_good_count_gt_three
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1)
    (hq : 2048≤Fintype.card K) :
    3 < Fintype.card
      {p : k4NormOnePairs (K:=K) //
        k4GeneralTraceGood (k4NormOneThetaTracePlane t) p} := by
  exact k4GeneralTraceGood_card_gt_three n hn hfinrank
    (k4NormOneThetaTracePlane t)
    (k4NormOneThetaTracePlane_card n hn hfinrank t ht0 ht1) hq

noncomputable def k4NormOneBadFirstPairs :=
  {p : k4NormOnePairs (K:=K) // p.val.1=0 ∨ p.val.1=1}

noncomputable instance k4NormOneBadFirstPairsFintype :
    Fintype (k4NormOneBadFirstPairs (K:=K)) := by
  classical
  unfold k4NormOneBadFirstPairs
  exact Fintype.ofFinite _

noncomputable def k4NormOneBadFirstPairCode
    (p : k4NormOneBadFirstPairs (K:=K)) : Fin 3 :=
  if p.val.val.1=0 then 0 else if p.val.val.2=0 then 1 else 2

omit [Fintype K] in
theorem k4NormOneBadFirstPairCode_injective :
    Function.Injective (k4NormOneBadFirstPairCode (K:=K)) := by
  classical
  intro p q hpq
  rcases p.property with hp0 | hp1
  · have hpu : p.val.val.2=1 :=
      k4_normOne_second_eq_one_of_first_eq_zero p.val.val.1 p.val.val.2
        p.val.property hp0
    rcases q.property with hq0 | hq1
    · have hqu : q.val.val.2=1 :=
        k4_normOne_second_eq_one_of_first_eq_zero q.val.val.1 q.val.val.2
          q.val.property hq0
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hp0.trans hq0.symm
      · exact hpu.trans hqu.symm
    · have hbad : k4NormOneBadFirstPairCode p ≠
          k4NormOneBadFirstPairCode q := by
        by_cases hqu0 : q.val.val.2=0 <;>
          simp [k4NormOneBadFirstPairCode,hp0,hq1,hqu0]
      exact (hbad hpq).elim
  · rcases k4_normOne_exceptions_of_first_eq_one p.val.val.1
        p.val.val.2 p.val.property hp1 with hpu | hpu
    · have hpc : k4NormOneBadFirstPairCode p=1 := by
        simp [k4NormOneBadFirstPairCode,hp1,hpu]
      rcases q.property with hq0 | hq1
      · have hqc : k4NormOneBadFirstPairCode q=0 := by
          simp [k4NormOneBadFirstPairCode,hq0]
        have : (1:Fin 3)=0 := by rw [← hpc, hpq, hqc]
        norm_num at this
      · rcases k4_normOne_exceptions_of_first_eq_one q.val.val.1
            q.val.val.2 q.val.property hq1 with hqu | hqu
        · have hqc : k4NormOneBadFirstPairCode q=1 := by
            simp [k4NormOneBadFirstPairCode,hq1,hqu]
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact hp1.trans hq1.symm
          · exact hpu.trans hqu.symm
        · have hqc : k4NormOneBadFirstPairCode q=2 := by
            simp [k4NormOneBadFirstPairCode,hq1,hqu]
          have : (1:Fin 3)=2 := by rw [← hpc, hpq, hqc]
          exact False.elim ((by decide : (1:Fin 3)≠2) this)
    · have hpc : k4NormOneBadFirstPairCode p=2 := by
        simp [k4NormOneBadFirstPairCode,hp1,hpu]
      rcases q.property with hq0 | hq1
      · have hqc : k4NormOneBadFirstPairCode q=0 := by
          simp [k4NormOneBadFirstPairCode,hq0]
        have : (2:Fin 3)=0 := by rw [← hpc, hpq, hqc]
        exact False.elim ((by decide : (2:Fin 3)≠0) this)
      · rcases k4_normOne_exceptions_of_first_eq_one q.val.val.1
            q.val.val.2 q.val.property hq1 with hqu | hqu
        · have hqc : k4NormOneBadFirstPairCode q=1 := by
            simp [k4NormOneBadFirstPairCode,hq1,hqu]
          have : (2:Fin 3)=1 := by rw [← hpc, hpq, hqc]
          exact False.elim ((by decide : (2:Fin 3)≠1) this)
        · have hqc : k4NormOneBadFirstPairCode q=2 := by
            simp [k4NormOneBadFirstPairCode,hq1,hqu]
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact hp1.trans hq1.symm
          · exact hpu.trans hqu.symm

theorem k4NormOneBadFirstPairs_card_le_three :
    Fintype.card (k4NormOneBadFirstPairs (K:=K))≤3 := by
  classical
  have hinj := k4NormOneBadFirstPairCode_injective (K:=K)
  have hle := Fintype.card_le_of_injective
    (k4NormOneBadFirstPairCode (K:=K)) hinj
  simpa using hle

theorem k4NormOneThetaTracePlane_exists_nondegenerate
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1)
    (hq : 2048≤Fintype.card K) :
    ∃ p : k4NormOnePairs (K:=K),
      k4GeneralTraceGood (k4NormOneThetaTracePlane t) p ∧
      p.val.1≠0 ∧ p.val.1≠1 := by
  classical
  let Good := {p : k4NormOnePairs (K:=K) //
    k4GeneralTraceGood (k4NormOneThetaTracePlane t) p}
  have hcount : 3<Fintype.card Good := by
    simpa [Good] using
      k4NormOneThetaTracePlane_good_count_gt_three n hn hfinrank t ht0 ht1 hq
  have hexists : ¬ ∀ p : Good, p.val.val.1=0 ∨ p.val.val.1=1 := by
    intro hall
    let f : Good → k4NormOneBadFirstPairs (K:=K) := fun p =>
      ⟨p.val, hall p⟩
    have hinj : Function.Injective f := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg (fun r : k4NormOneBadFirstPairs (K:=K) => r.val) hpq
    have hle := Fintype.card_le_of_injective f hinj
    have hle' : Fintype.card Good≤3 := by
      calc
        Fintype.card Good≤Fintype.card
            (k4NormOneBadFirstPairs (K:=K)) := hle
        _≤3 := k4NormOneBadFirstPairs_card_le_three
    omega
  obtain ⟨p,hp⟩ := not_forall.mp hexists
  let q : k4NormOnePairs (K:=K) := p.val
  have hp0 : q.val.1≠0 := by
    intro h
    apply hp
    exact Or.inl (by simpa [q] using h)
  have hp1 : q.val.1≠1 := by
    intro h
    apply hp
    exact Or.inr (by simpa [q] using h)
  exact ⟨q,p.property,hp0,hp1⟩

theorem k4NormOneThetaTracePlane_preimage
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t a : K)
    (htrace : ∀ w ∈ k4NormOneThetaTracePlane t,
      Algebra.trace (ZMod 2) K (w*a)=0) :
    ∃ x : K,
      (rootProduct (underlyingFinset (k4TracePlane t))).eval x =
        (t^2+t+1)^2*a := by
  have hc : t^2+t+1≠0 := by
    simpa [k4ASD] using k4ASD_ne_zero_of_odd_finrank n hn hfinrank t
  have horth : a ∈ traceOrthogonal (k4NormOneThetaTracePlane t) := by
    change a ∈ (Algebra.traceForm (ZMod 2) K).orthogonal
      (k4NormOneThetaTracePlane t)
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    simpa [Algebra.traceForm,mul_comm] using htrace w hw
  have hdouble :
      traceOrthogonal (k4NormOneThetaTracePlane t) =
        LinearMap.range (k4ScaledSubspacePolynomialMap
          (k4TracePlane t) ((t^2+t+1)⁻¹^2)) := by
    dsimp [k4NormOneThetaTracePlane]
    exact traceOrthogonal_involutive _
  rw [hdouble] at horth
  obtain ⟨x,hx⟩ := horth
  have hx' : (t^2+t+1)⁻¹^2 *
      (rootProduct (underlyingFinset (k4TracePlane t))).eval x = a := by
    simpa [k4ScaledSubspacePolynomialMap,k4ScalarMulMap,
      subspacePolynomialMap] using hx
  have hinv : (t^2+t+1)^2*(t^2+t+1)⁻¹^2=1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  refine ⟨x, ?_⟩
  calc
    (rootProduct (underlyingFinset (k4TracePlane t))).eval x =
        (t^2+t+1)^2 * ((t^2+t+1)⁻¹^2 *
          (rootProduct (underlyingFinset (k4TracePlane t))).eval x) := by
      calc
        _ = 1 * (rootProduct (underlyingFinset (k4TracePlane t))).eval x := by simp
        _ = ((t^2+t+1)^2*(t^2+t+1)⁻¹^2) *
              (rootProduct (underlyingFinset (k4TracePlane t))).eval x := by
            rw [hinv]
        _ = _ := by ring
    _ = (t^2+t+1)^2*a := by rw [hx']

omit [Fintype K] [DecidableEq K] in
theorem k4SpecialP3_coeff_four (x : Fin 4 → K) :
    (k4SpecialP3 x).coeff 4 =
      (k4SpecialP2 x).coeff 2^2+
        (k4SpecialP2 x).eval (x 2) := by
  change (k4UniversalP3.map (k4SpecialHom x)).coeff 4 = _
  rw [Polynomial.coeff_map, coeff_four_P3]
  simp only [map_add, map_pow, k4SpecialP2, Polynomial.coeff_map, k4_map_eval,
    k4SpecialHom_X]

omit [Fintype K] [DecidableEq K] in
theorem k4TracePlane_eq_k4Plane (t : K) :
    k4TracePlane t=k4Plane t := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      change (1:K)∈k4Line ⊔ Submodule.span (ZMod 2) ({t}:Set K)
      exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · rw [hz]
      change t∈k4Line ⊔ Submodule.span (ZMod 2) ({t}:Set K)
      exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Submodule.subset_span (by simp)
    · apply Submodule.span_le.mpr
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Submodule.subset_span (by simp)

omit [Fintype K] in
omit [Fintype K] [DecidableEq K] in
theorem k4NormOneTheta_t_not_in_line (t : K)
    (ht0 : t≠0) (ht1 : t≠1) : t∉k4Line := by
  intro ht
  have hcases : t=0 ∨ t=1 := by
    simpa [k4Line] using (mem_span_singleton_two (1:K) t).mp ht
  rcases hcases with h | h
  · exact ht0 h
  · exact ht1 h

theorem k4NormOneTheta_hasZeroSum_four_of_count
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (t : K) (ht0 : t≠0) (ht1 : t≠1)
    (hq : 2048≤Fintype.card K) : HasZeroSumSubspace K 4 := by
  obtain ⟨p,hgood,ha0,ha1⟩ :=
    k4NormOneThetaTracePlane_exists_nondegenerate n hn hfinrank t ht0 ht1 hq
  let a : K := p.val.1
  let u : K := p.val.2
  let c : K := t^2+t+1
  have hc : c≠0 := by
    simpa [c,k4ASD] using k4ASD_ne_zero_of_odd_finrank n hn hfinrank t
  have htraceA : ∀ w ∈ k4NormOneThetaTracePlane t,
      Algebra.trace (ZMod 2) K (w*a)=0 := by
    intro w hw
    have hu := hgood.1 w hw
    have hau := hgood.2 w hw
    have hsplit : Algebra.trace (ZMod 2) K (w*(a+u)) =
        Algebra.trace (ZMod 2) K (w*a)+Algebra.trace (ZMod 2) K (w*u) := by
      rw [mul_add, map_add]
    rw [hau,hu] at hsplit
    simpa using hsplit.symm
  obtain ⟨x,hx⟩ := k4NormOneThetaTracePlane_preimage
    n hn hfinrank t a htraceA
  obtain ⟨y,hy⟩ := k4NormOneThetaTracePlane_preimage
    n hn hfinrank t u hgood.1
  let z : Fin 4 → K := ![1,t,x,y]
  have htline := k4NormOneTheta_t_not_in_line t ht0 ht1
  have h0 : z 0≠0 := by simp [z]
  have h1 : z 1∉k4Span1 z := by
    simpa [z,k4Span1,k4Line] using htline
  have hspan : k4Span2 z=k4TracePlane t := by
    calc
      k4Span2 z=k4Plane t := by
        simp [k4Span2,k4Span1,k4Plane,k4Line,z]
      _=k4TracePlane t := (k4TracePlane_eq_k4Plane t).symm
  have hp1 := k4Span1_polynomial z h0
  have hp2 : rootProduct (underlyingFinset (k4Span2 z)) = k4SpecialP2 z := by
    rw [k4Span2, subspacePolynomial_extension _ _ h1, hp1, k4SpecialP2_eq]
  have hEvalX : (k4SpecialP2 z).eval x=c^2*a := by
    calc
      (k4SpecialP2 z).eval x=
          (rootProduct (underlyingFinset (k4Span2 z))).eval x := by rw [hp2]
      _=(rootProduct (underlyingFinset (k4TracePlane t))).eval x := by rw [hspan]
      _=c^2*a := by simpa [a,c] using hx
  have hEvalY : (k4SpecialP2 z).eval y=c^2*u := by
    calc
      (k4SpecialP2 z).eval y=
          (rootProduct (underlyingFinset (k4Span2 z))).eval y := by rw [hp2]
      _=(rootProduct (underlyingFinset (k4TracePlane t))).eval y := by rw [hspan]
      _=c^2*u := by simpa [u,c] using hy
  have hEvalXz : (k4SpecialP2 z).eval (z 2)=c^2*a := by
    simpa [z] using hEvalX
  have hP2eq : k4SpecialP2 z=k4P2 t := by
    calc
      k4SpecialP2 z=(rootProduct (underlyingFinset (k4Span2 z))) := hp2.symm
      _=rootProduct (underlyingFinset (k4TracePlane t)) := by rw [hspan]
      _=rootProduct (underlyingFinset (k4Plane t)) := by
        rw [k4TracePlane_eq_k4Plane]
      _=k4P2 t := k4Plane_polynomial t htline
  have hcoeff2 : (k4SpecialP2 z).coeff 2=c := by
    rw [hP2eq,k4P2_coeff_two]
    dsimp [c]
    ring
  have hcoeff : (k4SpecialP3 z).coeff 4=c^2*(1+a) := by
    rw [k4SpecialP3_coeff_four z,hcoeff2,hEvalXz]
    ring
  have h1a : 1+a≠0 := by
    intro h
    have ha1' : a=1 := by
      simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp h).symm
    exact ha1 ha1'
  have hcoeff_ne : (k4SpecialP3 z).coeff 4≠0 := by
    rw [hcoeff]
    exact mul_ne_zero (pow_ne_zero 2 hc) h1a
  have h2 : z 2∉k4Span2 z := by
    intro hmem
    have hzero := (subspacePolynomial_eval_eq_zero_iff (k4Span2 z) x).mpr hmem
    rw [hp2,hEvalX] at hzero
    exact (mul_ne_zero (pow_ne_zero 2 hc) ha0) hzero
  have hnorm : a^2+a*u+u^2=1 := p.property
  have hnorm' : u^2+a*u=1+a^2 := by
    have hsum := congrArg (fun v : K => v+a^2) hnorm
    have hcancel : a^2+a^2=0 := CharTwo.add_self_eq_zero (a^2)
    have hinner : a^2+(a^2+u^2)=u^2 := by
      calc
        a^2+(a^2+u^2)=(a^2+a^2)+u^2 := by ac_rfl
        _=u^2 := by rw [hcancel, zero_add]
    have hsum' : a*u+(a^2+(a^2+u^2))=1+a^2 := by
      calc
        a*u+(a^2+(a^2+u^2))=a^2+a*u+u^2+a^2 := by ac_rfl
        _=1+a^2 := hsum
    calc
      u^2+a*u=a*u+u^2 := by ac_rfl
      _=a*u+(a^2+(a^2+u^2)) := by rw [hinner]
      _=1+a^2 := hsum'
  have heval : (k4SpecialP3 z).eval y=c^4*(u^2+a*u) := by
    rw [k4SpecialP3_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [hEvalXz,hEvalY]
    ring
  have himage : (k4SpecialP3 z).coeff 4^2 ∈
      Set.range (k4SpecialP3 z).eval := by
    refine ⟨y, ?_⟩
    calc
      (k4SpecialP3 z).eval y=c^4*(u^2+a*u) := heval
      _=c^4*(1+a^2) := by rw [hnorm']
      _=(c^2*(1+a))^2 := by
        have hsquare : (1+a)^2=1+a^2 := by
          ring_nf
          have htwo : (2:K)=0 := CharP.cast_eq_zero K 2
          rw [htwo]
          ring
        rw [← hsquare]
        ring
      _=(k4SpecialP3 z).coeff 4^2 := by
        rw [hcoeff]
  exact hasZeroSumSubspace_four_of_three_space_image
    z h0 h1 h2 hcoeff_ne himage

theorem k4NormOneTheta_hasZeroSum_four_large
    (n : ℕ) (hn : Odd n) (hlarge : 11≤n)
    (hfinrank : Module.finrank (ZMod 2) K=n) :
    HasZeroSumSubspace K 4 := by
  classical
  have hcardPow : Fintype.card K=2^n := by
    have h := Module.card_eq_pow_finrank (K:=ZMod 2) (V:=K)
    simpa [Nat.card_eq_fintype_card,ZMod.card,hfinrank] using h
  have hq : 2048≤Fintype.card K := by
    rw [hcardPow]
    calc
      2048=2^11 := by norm_num
      _≤2^n := Nat.pow_le_pow_right (by norm_num) hlarge
  have ht : ∃ t : K, t≠0 ∧ t≠1 := by
    by_contra h
    have hcase : ∀ x : K, x=0 ∨ x=1 := by
      intro x
      by_cases hx : x=0
      · exact Or.inl hx
      · by_cases hx1 : x=1
        · exact Or.inr hx1
        · exact False.elim (h ⟨x,hx,hx1⟩)
    let f : K → Fin 2 := fun x => if x=0 then 0 else 1
    have hf : Function.Injective f := by
      intro x y hxy
      rcases hcase x with hx | hx <;> rcases hcase y with hy | hy
      · exact hx.trans hy.symm
      · simp [f,hx,hy] at hxy
      · simp [f,hx,hy] at hxy
      · exact hx.trans hy.symm
    have hle := Fintype.card_le_of_injective f hf
    simp at hle
    omega
  obtain ⟨t,ht0,ht1⟩ := ht
  exact k4NormOneTheta_hasZeroSum_four_of_count n hn hfinrank t ht0 ht1 hq

#print axioms k4ScaledSubspacePolynomialMap_ker
#print axioms k4NormOneThetaTracePlane_finrank
#print axioms k4NormOneThetaTracePlane_card
#print axioms k4NormOneThetaTracePlane_good_count_gt_three
#print axioms k4NormOneBadFirstPairCode_injective
#print axioms k4NormOneBadFirstPairs_card_le_three
#print axioms k4NormOneThetaTracePlane_exists_nondegenerate
#print axioms k4NormOneThetaTracePlane_preimage
#print axioms k4SpecialP3_coeff_four
#print axioms k4TracePlane_eq_k4Plane
#print axioms k4NormOneTheta_hasZeroSum_four_of_count
#print axioms k4NormOneTheta_hasZeroSum_four_large

end Carlet
