import Carlet.IncidenceCounting
import Mathlib.FieldTheory.Finite.Basic

noncomputable section

namespace Carlet

/-- Over `F₂`, a finite-dimensional vector space and its linear dual have the
same dimension. This is the dimension input for counting annihilating
functionals in the fixed-vector hyperplane count. -/
theorem binaryDual_finrank_eq {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W] :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) =
      Module.finrank (ZMod 2) W := by
  exact (LinearEquiv.finrank_eq (Module.finBasis (ZMod 2) W).toDualEquiv).symm

set_option linter.style.haveILetI false in
theorem binaryDual_card_eq_pow {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W] :
    Nat.card (Module.Dual (ZMod 2) W) =
      2 ^ Module.finrank (ZMod 2) W := by
  classical
  let b := Module.finBasis (ZMod 2) W
  let bDual := b.dualBasis
  letI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f => bDual.repr f) bDual.repr.injective
  letI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  have htwo : Fintype.card (ZMod 2) = 2 := by decide
  calc
    Nat.card (Module.Dual (ZMod 2) W) = Fintype.card (Module.Dual (ZMod 2) W) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (ZMod 2) ^
        Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) :=
      Module.card_eq_pow_finrank
    _ = 2 ^ Module.finrank (ZMod 2) W := by
      rw [htwo, binaryDual_finrank_eq]

theorem binaryScalar_eq_zero_or_one (y : ZMod 2) : y = 0 ∨ y = 1 := by
  fin_cases y
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem binaryFunctional_ker_codim_one {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (f : W →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    Module.finrank (ZMod 2) f.ker + 1 = Module.finrank (ZMod 2) W := by
  have hsurj : Function.Surjective f := by
    intro y
    rcases binaryScalar_eq_zero_or_one y with hy0 | hy1
    · subst y
      exact ⟨0, by simp⟩
    · subst y
      have hex : ∃ x : W, f x ≠ 0 := by
        by_contra h
        push Not at h
        apply hf
        ext x
        simpa using h x
      obtain ⟨x, hx⟩ := hex
      have hx1 : f x = 1 := by
        rcases binaryScalar_eq_zero_or_one (f x) with hzero | hone
        · exact (hx hzero).elim
        · exact hone
      exact ⟨x, hx1⟩
  have hquot := LinearMap.quotKerEquivOfSurjective f hsurj
  have hdimquot : Module.finrank (ZMod 2) (W ⧸ f.ker) = 1 := by
    simpa using (LinearEquiv.finrank_eq hquot)
  have hsum := f.ker.finrank_quotient_add_finrank
  rw [hdimquot] at hsum
  omega

def binaryHyperplanes (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W] :=
  {H : Submodule (ZMod 2) W // Module.finrank (ZMod 2) H + 1 =
    Module.finrank (ZMod 2) W}

def nonzeroBinaryFunctionals (W : Type*) [AddCommGroup W]
    [Module (ZMod 2) W] :=
  {f : W →ₗ[ZMod 2] ZMod 2 // f ≠ 0}

def binaryHyperplanesContaining {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (v : W) := {H : binaryHyperplanes W // v ∈ H.val}

def binaryFunctionalsVanishing {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (v : W) :=
  {f : nonzeroBinaryFunctionals W // f.val v = 0}

def binaryEvalAt {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : W) : Module.Dual (ZMod 2) W →ₗ[ZMod 2] ZMod 2 :=
  Module.Dual.eval (ZMod 2) W v

theorem binaryHyperplane_quotient_finrank {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (H : binaryHyperplanes W) :
    Module.finrank (ZMod 2) (W ⧸ H.val) = 1 := by
  have hsum := H.val.finrank_quotient_add_finrank
  have hdim := H.property
  omega

noncomputable def binaryHyperplaneQuotEquiv {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (H : binaryHyperplanes W) : (W ⧸ H.val) ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofFinrankEq (W ⧸ H.val) (ZMod 2) (by
    rw [binaryHyperplane_quotient_finrank]
    simp)

noncomputable def binaryFunctionalOfHyperplane {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (H : binaryHyperplanes W) : W →ₗ[ZMod 2] ZMod 2 :=
  (binaryHyperplaneQuotEquiv H).toLinearMap.comp H.val.mkQ

theorem ker_binaryFunctionalOfHyperplane {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (H : binaryHyperplanes W) :
    (binaryFunctionalOfHyperplane H).ker = H.val := by
  ext x
  change binaryFunctionalOfHyperplane H x = 0 ↔ x ∈ H.val
  constructor
  · intro hx
    have hqx : H.val.mkQ x = 0 := by
      apply (binaryHyperplaneQuotEquiv H).injective
      simpa [binaryFunctionalOfHyperplane] using hx
    have hker : x ∈ H.val.mkQ.ker := LinearMap.mem_ker.mpr hqx
    rwa [Submodule.ker_mkQ] at hker
  · intro hx
    have hqx : H.val.mkQ x = 0 := by
      apply LinearMap.mem_ker.mp
      rwa [Submodule.ker_mkQ]
    simp [binaryFunctionalOfHyperplane, hqx]

theorem binaryFunctionalOfHyperplane_ne_zero {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (H : binaryHyperplanes W) : binaryFunctionalOfHyperplane H ≠ 0 := by
  intro hf
  have hnotTop : H.val ≠ ⊤ := by
    intro htop
    have hdim := H.property
    rw [htop, finrank_top] at hdim
    omega
  have hex : ∃ x : W, x ∉ H.val := by
    by_contra h
    push Not at h
    apply hnotTop
    apply top_unique
    intro x hx
    exact h x
  obtain ⟨x, hx⟩ := hex
  have hqx : H.val.mkQ x ≠ 0 := by
    intro hzero
    apply hx
    have hker : x ∈ H.val.mkQ.ker := LinearMap.mem_ker.mpr hzero
    rwa [Submodule.ker_mkQ] at hker
  have hval : binaryFunctionalOfHyperplane H x = 0 := by
    have h := congrArg (fun f : W →ₗ[ZMod 2] ZMod 2 => f x) hf
    simpa using h
  have : H.val.mkQ x = 0 := by
    apply (binaryHyperplaneQuotEquiv H).injective
    simpa [binaryFunctionalOfHyperplane] using hval
  exact hqx this

theorem binaryFunctionals_eq_of_ker_eq {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (f g : W →ₗ[ZMod 2] ZMod 2)
    (hker : f.ker = g.ker) : f = g := by
  ext x
  rcases binaryScalar_eq_zero_or_one (f x) with hfx0 | hfx1
  · have hxker : x ∈ f.ker := LinearMap.mem_ker.mpr hfx0
    have hxker' : x ∈ g.ker := by simpa [hker] using hxker
    rw [hfx0, LinearMap.mem_ker.mp hxker']
  · have hxnotker : x ∉ f.ker := by
      intro hx
      exact one_ne_zero (hfx1.symm.trans (LinearMap.mem_ker.mp hx))
    have hxnotker' : x ∉ g.ker := by simpa [hker] using hxnotker
    have hgx0 : g x ≠ 0 := by
      intro hgx
      exact hxnotker' (LinearMap.mem_ker.mpr hgx)
    rcases binaryScalar_eq_zero_or_one (g x) with hcase0 | hgx1
    · exact False.elim (hgx0 hcase0)
    · rw [hfx1, hgx1]

noncomputable def binaryHyperplaneOfFunctional {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (f : nonzeroBinaryFunctionals W) : binaryHyperplanes W :=
  ⟨f.val.ker, binaryFunctional_ker_codim_one f.val f.property⟩

noncomputable def binaryHyperplaneFunctionalEquiv {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W] :
    nonzeroBinaryFunctionals W ≃ binaryHyperplanes W where
  toFun := binaryHyperplaneOfFunctional
  invFun H := ⟨binaryFunctionalOfHyperplane H, binaryFunctionalOfHyperplane_ne_zero H⟩
  left_inv f := by
    apply Subtype.ext
    exact (binaryFunctionals_eq_of_ker_eq f.val
      (binaryFunctionalOfHyperplane (binaryHyperplaneOfFunctional f))
      (by
        rw [ker_binaryFunctionalOfHyperplane]
        rfl)).symm
  right_inv H := by
    apply Subtype.ext
    exact ker_binaryFunctionalOfHyperplane H

noncomputable def binaryHyperplaneContainingFunctionalEquiv
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W] (v : W) :
    binaryHyperplanesContaining v ≃ binaryFunctionalsVanishing v where
  toFun H := by
    let f := (binaryHyperplaneFunctionalEquiv (W := W)).symm H.val
    have hker : f.val.ker = H.val.val := by
      change (binaryHyperplaneOfFunctional f).val = H.val.val
      exact congrArg Subtype.val
        ((binaryHyperplaneFunctionalEquiv (W := W)).apply_symm_apply H.val)
    have hv : v ∈ f.val.ker := by rw [hker]; exact H.property
    exact ⟨f, LinearMap.mem_ker.mp hv⟩
  invFun f := by
    refine ⟨binaryHyperplaneFunctionalEquiv (W := W) f.val, ?_⟩
    change v ∈ f.val.val.ker
    exact LinearMap.mem_ker.mpr f.property
  left_inv H := by
    apply Subtype.ext
    exact (binaryHyperplaneFunctionalEquiv (W := W)).apply_symm_apply H.val
  right_inv f := by
    apply Subtype.ext
    exact (binaryHyperplaneFunctionalEquiv (W := W)).symm_apply_apply f.val

theorem binaryEvalAt_ne_zero {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (v : W) (hv : v ≠ 0) : binaryEvalAt v ≠ 0 := by
  intro heval
  let b := Module.finBasis (ZMod 2) W
  have hrepr : b.repr v ≠ 0 := by
    intro h
    apply hv
    apply b.repr.injective
    simpa using h
  have hex : ∃ i, (b.repr v) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hdual : (b.dualBasis i) v ≠ 0 := by
    simpa [Module.Basis.dualBasis_apply] using hi
  have hzero : (b.dualBasis i) v = 0 := by
    have h := congrArg (fun e : Module.Dual (ZMod 2) (Module.Dual (ZMod 2) W) =>
      e (b.dualBasis i)) heval
    simpa [binaryEvalAt, Module.Dual.eval] using h
  exact hdual hzero

noncomputable def binaryFunctionalsVanishingEquivKernelNonzero
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (v : W) :
    binaryFunctionalsVanishing v ≃
      {f : (binaryEvalAt v).ker // f ≠ 0} where
  toFun f := by
    refine ⟨⟨f.val.val, ?_⟩, ?_⟩
    · apply LinearMap.mem_ker.mpr
      simpa [binaryEvalAt, Module.Dual.eval] using f.property
    · intro h
      exact f.val.property (congrArg Subtype.val h)
  invFun f := by
    refine ⟨⟨f.val.val, ?_⟩, ?_⟩
    · intro h
      apply f.property
      apply Subtype.ext
      exact h
    · have h := LinearMap.mem_ker.mp f.val.property
      change f.val.val v = 0
      exact h
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

set_option linter.style.haveILetI false in
theorem binarySubmoduleNonzero_card {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Fintype W] (E : Submodule (ZMod 2) W) (d : ℕ)
    (hd : Module.finrank (ZMod 2) E = d) :
    Nat.card {x : E // x ≠ 0} = 2 ^ d - 1 := by
  classical
  letI : Fintype E := Fintype.ofFinite _
  have hz : (0 : E) ∈ (Finset.univ : Finset E) := Finset.mem_univ _
  have hcard : Nat.card {x : E // x ≠ 0} =
      ((Finset.univ : Finset E).erase 0).card := by
    calc
      _ = Fintype.card {x : E // x ≠ 0} := Nat.card_eq_fintype_card
      _ = (Finset.univ.filter fun x : E => x ≠ 0).card := Fintype.card_subtype _
      _ = ((Finset.univ : Finset E).erase 0).card := by
        congr 1
        ext x
        simp [Finset.mem_erase]
  rw [hcard]
  have hsize : ((Finset.univ : Finset E).erase 0).card + 1 = Fintype.card E :=
    Finset.card_erase_add_one hz
  have htwo : Fintype.card (ZMod 2) = 2 := by decide
  have hpow : Fintype.card E = 2 ^ d := by
    calc
      Fintype.card E = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) E :=
        Module.card_eq_pow_finrank
      _ = 2 ^ d := by rw [htwo, hd]
  omega

set_option linter.style.haveILetI false in
theorem binaryHyperplanesContaining_card {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Free (ZMod 2) W] [Module.Finite (ZMod 2) W]
    [Fintype W] (v : W) (hv : v ≠ 0) :
    Nat.card (binaryHyperplanesContaining v) =
      2 ^ (Module.finrank (ZMod 2) W - 1) - 1 := by
  classical
  let b := Module.finBasis (ZMod 2) W
  let bDual := b.dualBasis
  letI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f => bDual.repr f) bDual.repr.injective
  letI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  let ev := binaryEvalAt v
  have hev : ev ≠ 0 := binaryEvalAt_ne_zero v hv
  have hker := binaryFunctional_ker_codim_one ev hev
  have hdual := binaryDual_finrank_eq (W := W)
  have hdim : Module.finrank (ZMod 2) ev.ker =
      Module.finrank (ZMod 2) W - 1 := by omega
  calc
    Nat.card (binaryHyperplanesContaining v) = Nat.card (binaryFunctionalsVanishing v) :=
      Nat.card_congr (binaryHyperplaneContainingFunctionalEquiv v)
    _ = Nat.card {f : ev.ker // f ≠ 0} :=
      Nat.card_congr (binaryFunctionalsVanishingEquivKernelNonzero v)
    _ = 2 ^ (Module.finrank (ZMod 2) W - 1) - 1 := by
      exact binarySubmoduleNonzero_card ev.ker _ hdim

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def binaryLine (P : Submodule (ZMod 2) V) : Prop :=
  Module.finrank (ZMod 2) P = 1

def binaryLines : Type _ := {P : Submodule (ZMod 2) V // binaryLine P}

def lineOfNonzeroVector (x : {x : V // x ≠ 0}) : binaryLines (V := V) := by
  refine ⟨(ZMod 2) ∙ x.val, ?_⟩
  exact finrank_span_singleton x.property

theorem binaryLine_ne_bot (P : binaryLines (V := V)) : P.val ≠ ⊥ := by
  intro h
  have hdim : Module.finrank (ZMod 2) P.val = 1 := P.property
  rw [h] at hdim
  simp at hdim

noncomputable def binaryLineGenerator (P : binaryLines (V := V)) : V :=
  Classical.choose ((Submodule.ne_bot_iff P.val).mp (binaryLine_ne_bot P))

theorem binaryLineGenerator_spec (P : binaryLines (V := V)) :
    binaryLineGenerator P ∈ P.val ∧ binaryLineGenerator P ≠ 0 :=
  Classical.choose_spec ((Submodule.ne_bot_iff P.val).mp (binaryLine_ne_bot P))

noncomputable def nonzeroVectorBinaryLineEquiv :
    {x : V // x ≠ 0} ≃ binaryLines (V := V) where
  toFun := lineOfNonzeroVector
  invFun P := ⟨binaryLineGenerator P, (binaryLineGenerator_spec P).2⟩
  left_inv x := by
    apply Subtype.ext
    have hmem : binaryLineGenerator (lineOfNonzeroVector x) ∈
        (ZMod 2) ∙ x.val := by
      simpa [lineOfNonzeroVector] using
        (binaryLineGenerator_spec (lineOfNonzeroVector x)).1
    rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
    have hc1 : c = 1 := by
      fin_cases c
      · simp at hc
        have hgen0 : binaryLineGenerator (lineOfNonzeroVector x) = 0 := by
          calc
            binaryLineGenerator (lineOfNonzeroVector x) = (0 : ZMod 2) • x.val := hc.symm
            _ = 0 := zero_smul _ _
        exact False.elim ((binaryLineGenerator_spec (lineOfNonzeroVector x)).2 hgen0)
      · rfl
    simpa [hc1] using hc.symm
  right_inv P := by
    apply Subtype.ext
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact (binaryLineGenerator_spec P).1
    · intro y hy
      let xP : P.val := ⟨binaryLineGenerator P, (binaryLineGenerator_spec P).1⟩
      let yP : P.val := ⟨y, hy⟩
      have hxP : xP ≠ 0 := by
        intro h
        exact (binaryLineGenerator_spec P).2 (congrArg Subtype.val h)
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one P.property hxP yP
      have hval : c • binaryLineGenerator P = y := by
        simpa [xP, yP] using congrArg Subtype.val hc
      change y ∈ (ZMod 2) ∙ binaryLineGenerator P
      rw [← hval]
      exact Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self (binaryLineGenerator P))

set_option linter.style.haveILetI false in
/-- Pulling a binary line in `K ⧸ E` back along the quotient map raises the
dimension of `E` by exactly one. This is the dimension part of the
correspondence between quotient lines and adjacent-dimensional extensions. -/
theorem finrank_comap_binaryLine (d : ℕ) (E : Submodule (ZMod 2) K)
    (hd : Module.finrank (ZMod 2) E = d)
    (P : binaryLines (V := K ⧸ E)) :
    Module.finrank (ZMod 2) ↥(P.val.comap E.mkQ) = d + 1 := by
  classical
  let x : K := Classical.choose
    (Submodule.mkQ_surjective E (binaryLineGenerator P))
  have hxq : E.mkQ x = binaryLineGenerator P :=
    Classical.choose_spec
      (Submodule.mkQ_surjective E (binaryLineGenerator P))
  have hx_not_E : x ∉ E := by
    intro h
    have hx0 : E.mkQ x = 0 := by
      have hker : x ∈ E.mkQ.ker := by rwa [Submodule.ker_mkQ]
      exact LinearMap.mem_ker.mp hker
    exact (binaryLineGenerator_spec P).2 (hxq.symm.trans hx0)
  have hx0 : x ≠ 0 := by
    intro h
    apply hx_not_E
    simp [h]
  let L : Submodule (ZMod 2) K := (ZMod 2) ∙ x
  have hF : P.val.comap E.mkQ = E ⊔ L := by
    apply le_antisymm
    · intro y hy
      have hqy : E.mkQ y ∈ P.val := Submodule.mem_comap.mp hy
      let xP : P.val := ⟨binaryLineGenerator P,
        (binaryLineGenerator_spec P).1⟩
      let yP : P.val := ⟨E.mkQ y, hqy⟩
      have hxP : xP ≠ 0 := by
        intro h
        exact (binaryLineGenerator_spec P).2 (congrArg Subtype.val h)
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one P.property hxP yP
      have hqeq : c • binaryLineGenerator P = E.mkQ y := by
        simpa [xP, yP] using congrArg Subtype.val hc
      have hdiff : E.mkQ (y - c • x) = 0 := by
        rw [map_sub, map_smul, hxq, hqeq]
        exact sub_self _
      have hdiffE : y - c • x ∈ E := by
        have hker : y - c • x ∈ E.mkQ.ker := LinearMap.mem_ker.mpr hdiff
        rwa [Submodule.ker_mkQ] at hker
      apply Submodule.mem_sup.mpr
      refine ⟨y - c • x, hdiffE, c • x, ?_, ?_⟩
      · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · simp
    · intro y hy
      rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
      change E.mkQ y ∈ P.val
      rw [← hab, map_add]
      have hEa : E.mkQ a = 0 := by
        have hker : a ∈ E.mkQ.ker := by rwa [Submodule.ker_mkQ]
        exact LinearMap.mem_ker.mp hker
      rcases Submodule.mem_span_singleton.mp hb with ⟨c, hc⟩
      rw [hEa, zero_add, ← hc, map_smul, hxq]
      exact Submodule.smul_mem P.val _ (binaryLineGenerator_spec P).1
  have hinter : E ⊓ L = ⊥ := by
    apply le_antisymm
    · intro y hy
      rcases Submodule.mem_inf.mp hy with ⟨hyE, hyL⟩
      rcases Submodule.mem_span_singleton.mp hyL with ⟨c, hcy⟩
      fin_cases c
      · simp at hcy
        subst y
        exact zero_smul _ _
      · have hxe : x ∈ E := by
          have hxy : x = y := by
            calc
              x = (1 : ZMod 2) • x := by simp
              _ = y := hcy
          rw [hxy]
          exact hyE
        exact False.elim (hx_not_E hxe)
    · exact bot_le
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq E L
  have hdimL : Module.finrank (ZMod 2) ↥L = 1 :=
    finrank_span_singleton hx0
  have hdimF : Module.finrank (ZMod 2) ↥(E ⊔ L) = d + 1 := by
    rw [hinter] at hsum
    simp [hdimL, hd] at hsum
    omega
  rw [hF]
  exact hdimF

omit [Fintype K] in
theorem comap_span_mkQ_eq_sup (E : Submodule (ZMod 2) K) (x : K) :
    ((ZMod 2) ∙ E.mkQ x).comap E.mkQ = E ⊔ (ZMod 2) ∙ x := by
  apply le_antisymm
  · intro y hy
    have hqy : E.mkQ y ∈ (ZMod 2) ∙ E.mkQ x := Submodule.mem_comap.mp hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hqy
    have hdiff : E.mkQ (y - c • x) = 0 := by
      rw [map_sub, map_smul, hc]
      simp
    have hdiffE : y - c • x ∈ E := by
      have hker : y - c • x ∈ E.mkQ.ker := LinearMap.mem_ker.mpr hdiff
      rwa [Submodule.ker_mkQ] at hker
    apply Submodule.mem_sup.mpr
    refine ⟨y - c • x, hdiffE, c • x, ?_, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · simp
  · intro y hy
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
    change E.mkQ y ∈ (ZMod 2) ∙ E.mkQ x
    rw [← hab, map_add]
    have hEa : E.mkQ a = 0 := by
      have hker : a ∈ E.mkQ.ker := by rwa [Submodule.ker_mkQ]
      exact LinearMap.mem_ker.mp hker
    rcases Submodule.mem_span_singleton.mp hb with ⟨c, hc⟩
    rw [hEa, zero_add, ← hc, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (E.mkQ x))

set_option linter.style.haveILetI false in
theorem finrank_comapMkQRelIso_symm_binaryLine (d : ℕ)
    (E F : Submodule (ZMod 2) K) (hd : Module.finrank (ZMod 2) E = d)
    (hEF : E ≤ F) (hF : Module.finrank (ZMod 2) F = d + 1) :
    Module.finrank (ZMod 2) ↥((E.comapMkQRelIso).symm ⟨F, hEF⟩) = 1 := by
  classical
  have hnot : ¬ F ≤ E := by
    intro hFE
    have hmono := Submodule.finrank_mono hFE
    rw [hF, hd] at hmono
    omega
  have hex : ∃ x, x ∈ F ∧ x ∉ E := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x, hxF, hxE⟩ := hex
  have hxq : E.mkQ x ≠ 0 := by
    intro hzero
    apply hxE
    have hker : x ∈ E.mkQ.ker := LinearMap.mem_ker.mpr hzero
    rwa [Submodule.ker_mkQ] at hker
  let Q : binaryLines (V := K ⧸ E) :=
    lineOfNonzeroVector ⟨E.mkQ x, hxq⟩
  let S : Submodule (ZMod 2) K := E ⊔ (ZMod 2) ∙ x
  have hcomapQ : Q.val.comap E.mkQ = S := by
    simpa [Q, S, lineOfNonzeroVector] using comap_span_mkQ_eq_sup E x
  have hSF : S ≤ F := by
    apply sup_le hEF
    apply Submodule.span_le.mpr
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hxF
  have hdimS : Module.finrank (ZMod 2) S = d + 1 := by
    calc
      Module.finrank (ZMod 2) S =
          Module.finrank (ZMod 2) ↥(Q.val.comap E.mkQ) := by rw [hcomapQ]
      _ = d + 1 := finrank_comap_binaryLine d E hd Q
  have hSeq : S = F :=
    Submodule.eq_of_le_of_finrank_eq hSF (by rw [hdimS, hF])
  let P : Submodule (ZMod 2) (K ⧸ E) :=
    (E.comapMkQRelIso).symm ⟨F, hEF⟩
  have hcomapP : P.comap E.mkQ = F := by
    change ((E.comapMkQRelIso) P).val = F
    have h := (E.comapMkQRelIso).apply_symm_apply ⟨F, hEF⟩
    exact congrArg Subtype.val h
  have hIso : E.comapMkQRelIso P = E.comapMkQRelIso Q.val := by
    apply Subtype.ext
    change P.comap E.mkQ = Q.val.comap E.mkQ
    rw [hcomapP, hcomapQ, hSeq]
  have hPQ : P = Q.val := (E.comapMkQRelIso).injective hIso
  change Module.finrank (ZMod 2) P = 1
  rw [hPQ]
  exact Q.property

def adjacentExtensions (d : ℕ) (E : Submodule (ZMod 2) K) : Type _ :=
  {F : Submodule (ZMod 2) K // E ≤ F ∧ Module.finrank (ZMod 2) F = d + 1}

noncomputable def binaryLineAdjacentExtensionEquiv (d : ℕ)
    (E : Submodule (ZMod 2) K) (hd : Module.finrank (ZMod 2) E = d) :
    binaryLines (V := K ⧸ E) ≃ adjacentExtensions (K := K) d E where
  toFun P :=
    ⟨(E.comapMkQRelIso P.val).val,
      ⟨(E.comapMkQRelIso P.val).property,
        finrank_comap_binaryLine d E hd P⟩⟩
  invFun F := by
    let P : Submodule (ZMod 2) (K ⧸ E) :=
      (E.comapMkQRelIso).symm ⟨F.val, F.property.1⟩
    have hdim : Module.finrank (ZMod 2) P = 1 :=
      finrank_comapMkQRelIso_symm_binaryLine d E F.val hd F.property.1 F.property.2
    exact ⟨P, hdim⟩
  left_inv P := by
    apply Subtype.ext
    exact (E.comapMkQRelIso).symm_apply_apply P.val
  right_inv F := by
    apply Subtype.ext
    change ((E.comapMkQRelIso)
      ((E.comapMkQRelIso).symm ⟨F.val, F.property.1⟩)).val = F.val
    exact congrArg Subtype.val
      ((E.comapMkQRelIso).apply_symm_apply ⟨F.val, F.property.1⟩)

noncomputable def submodulesBelowEquiv (F : Submodule (ZMod 2) K) :
    {E : Submodule (ZMod 2) K // E ≤ F} ≃ Submodule (ZMod 2) F where
  toFun E := E.val.comap F.subtype
  invFun H := ⟨H.map F.subtype, by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hmem : F.subtype y ∈ F := y.property
    rw [hxy] at hmem
    exact hmem⟩
  left_inv E := by
    apply Subtype.ext
    change (E.val.comap F.subtype).map F.subtype = E.val
    apply Submodule.map_comap_eq_self
    intro x hx
    exact ⟨⟨x, E.property hx⟩, rfl⟩
  right_inv H := by
    ext y
    rw [Submodule.mem_comap]
    change F.subtype y ∈ H.map F.subtype ↔ y ∈ H
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.val_injective hzy
      simpa [hzy'] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩

omit [Fintype K] in
theorem finrank_comap_submoduleBelow {F E : Submodule (ZMod 2) K}
    (hEF : E ≤ F) :
    Module.finrank (ZMod 2) (E.comap F.subtype) = Module.finrank (ZMod 2) E := by
  have hle : E ≤ F.subtype.range := by
    intro x hx
    exact ⟨⟨x, hEF hx⟩, rfl⟩
  calc
    Module.finrank (ZMod 2) (E.comap F.subtype) =
        Module.finrank (ZMod 2) ((E.comap F.subtype).map F.subtype) :=
      LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective F.subtype Subtype.val_injective
          (E.comap F.subtype))
    _ = Module.finrank (ZMod 2) E := by rw [Submodule.map_comap_eq_self hle]

def subspacesBelowOne (F : Submodule (ZMod 2) K) (d : ℕ) :=
  {E : Submodule (ZMod 2) K // E ≤ F ∧
    Module.finrank (ZMod 2) E = d ∧ (1 : K) ∈ E}

noncomputable def subspacesBelowOneEquivHyperplanes
    (F : Submodule (ZMod 2) K) (d : ℕ)
    (hFdim : Module.finrank (ZMod 2) F = d + 1) (h1F : (1 : K) ∈ F) :
    subspacesBelowOne F d ≃
      binaryHyperplanesContaining (⟨(1 : K), h1F⟩ : F) where
  toFun E := by
    refine ⟨⟨E.val.comap F.subtype, ?_⟩, ?_⟩
    · rw [finrank_comap_submoduleBelow E.property.1,
        E.property.2.1, hFdim]
    · change F.subtype ⟨(1 : K), h1F⟩ ∈ E.val
      simpa using E.property.2.2
  invFun H := by
    let E := (submodulesBelowEquiv F).symm H.val.val
    have hEq : E.val.comap F.subtype = H.val.val := by
      change submodulesBelowEquiv F E = H.val.val
      exact (submodulesBelowEquiv F).apply_symm_apply H.val.val
    have hcomapDim := finrank_comap_submoduleBelow E.property
    have hdimE : Module.finrank (ZMod 2) E.val = d := by
      have hHdim := H.val.property
      calc
        Module.finrank (ZMod 2) E.val =
            Module.finrank (ZMod 2) (E.val.comap F.subtype) := hcomapDim.symm
        _ = Module.finrank (ZMod 2) H.val.val := by rw [hEq]
        _ = d := by omega
    have h1E : (1 : K) ∈ E.val := by
      have hv : (⟨(1 : K), h1F⟩ : F) ∈ H.val.val := H.property
      rw [← hEq] at hv
      have hv' := Submodule.mem_comap.mp hv
      simpa using hv'
    exact ⟨E.val, E.property, hdimE, h1E⟩
  left_inv E := by
    apply Subtype.ext
    change ((submodulesBelowEquiv F).symm
      (submodulesBelowEquiv F ⟨E.val, E.property.1⟩)).val = E.val
    exact congrArg Subtype.val
      ((submodulesBelowEquiv F).symm_apply_apply ⟨E.val, E.property.1⟩)
  right_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    change submodulesBelowEquiv F ((submodulesBelowEquiv F).symm H.val.val) =
      H.val.val
    exact (submodulesBelowEquiv F).apply_symm_apply H.val.val

set_option linter.style.haveILetI false in
theorem subspacesBelowOne_card_eq_pow_sub_one
    (F : Submodule (ZMod 2) K) (d : ℕ)
    (hFdim : Module.finrank (ZMod 2) F = d + 1) (h1F : (1 : K) ∈ F) :
    Nat.card (subspacesBelowOne F d) = 2 ^ d - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite _
  let v : F := ⟨1, h1F⟩
  have hv : v ≠ 0 := by
    intro h
    have hval : (1 : K) = 0 := congrArg Subtype.val h
    exact one_ne_zero hval
  calc
    Nat.card (subspacesBelowOne F d) =
        Nat.card (binaryHyperplanesContaining v) :=
      Nat.card_congr (subspacesBelowOneEquivHyperplanes F d hFdim h1F)
    _ = 2 ^ (Module.finrank (ZMod 2) F - 1) - 1 :=
      binaryHyperplanesContaining_card v hv
    _ = 2 ^ d - 1 := by rw [hFdim]; simp

local instance flagSubmoduleFinite : Finite (Submodule (ZMod 2) K) :=
  Finite.of_injective (fun E : Submodule (ZMod 2) K => (E : Set K))
    SetLike.coe_injective

local instance oneFiberFinite (d : ℕ) :
    Finite (dimensionFiberContainingOne (K := K) d) :=
  Finite.of_injective
    (fun E : dimensionFiberContainingOne (K := K) d => E.val)
    Subtype.val_injective

local instance oneFiberFintype (d : ℕ) :
    Fintype (dimensionFiberContainingOne (K := K) d) := Fintype.ofFinite _

local instance adjacentExtensionsFinite (d : ℕ) (E : Submodule (ZMod 2) K) :
    Finite (adjacentExtensions (K := K) d E) :=
  Finite.of_injective (fun F : adjacentExtensions (K := K) d E => F.val)
    Subtype.val_injective

local instance adjacentExtensionsFintype (d : ℕ) (E : Submodule (ZMod 2) K) :
    Fintype (adjacentExtensions (K := K) d E) := Fintype.ofFinite _

local instance subspacesBelowOneFinite (F : Submodule (ZMod 2) K) (d : ℕ) :
    Finite (subspacesBelowOne F d) :=
  Finite.of_injective (fun E : subspacesBelowOne F d => E.val)
    Subtype.val_injective

local instance subspacesBelowOneFintype (F : Submodule (ZMod 2) K) (d : ℕ) :
    Fintype (subspacesBelowOne F d) := Fintype.ofFinite _

def adjacentOneFlags (d : ℕ) :=
  {p : dimensionFiberContainingOne (K := K) d ×
      dimensionFiberContainingOne (K := K) (d + 1) // p.1.val ≤ p.2.val}

def adjacentOneFlagsByLower (d : ℕ) :=
  Σ E : dimensionFiberContainingOne (K := K) d,
    {F : adjacentExtensions (K := K) d E.val // (1 : K) ∈ F.val}

def adjacentOneFlagsByUpper (d : ℕ) :=
  Σ F : dimensionFiberContainingOne (K := K) (d + 1),
    subspacesBelowOne F.val d

noncomputable def adjacentOneFlagsEquivByLower (d : ℕ) :
    adjacentOneFlags (K := K) d ≃ adjacentOneFlagsByLower (K := K) d where
  toFun p := by
    let F : adjacentExtensions (K := K) d p.val.1.val :=
      ⟨p.val.2.val, ⟨p.property, p.val.2.property.1⟩⟩
    exact ⟨p.val.1, ⟨F, p.val.2.property.2⟩⟩
  invFun p := by
    let F : dimensionFiberContainingOne (K := K) (d + 1) :=
      ⟨p.2.val.val, ⟨p.2.val.property.2, p.2.property⟩⟩
    exact ⟨(p.1, F), p.2.val.property.1⟩
  left_inv p := by
    rcases p with ⟨⟨E, F⟩, h⟩
    rfl
  right_inv p := by
    rcases p with ⟨E, ⟨F, h1F⟩⟩
    rfl

noncomputable def adjacentOneFlagsEquivByUpper (d : ℕ) :
    adjacentOneFlags (K := K) d ≃ adjacentOneFlagsByUpper (K := K) d where
  toFun p := by
    let E : subspacesBelowOne p.val.2.val d :=
      ⟨p.val.1.val, p.property,
        p.val.1.property.1, p.val.1.property.2⟩
    exact ⟨p.val.2, E⟩
  invFun p := by
    let E : dimensionFiberContainingOne (K := K) d :=
      ⟨p.2.val, ⟨p.2.property.2.1, p.2.property.2.2⟩⟩
    exact ⟨(E, p.1), p.2.property.1⟩
  left_inv p := by
    rcases p with ⟨⟨E, F⟩, h⟩
    rfl
  right_inv p := by
    rcases p with ⟨F, E⟩
    rfl

noncomputable def adjacentExtensionsContainingOneEquiv (d : ℕ)
    (E : dimensionFiberContainingOne (K := K) d) :
    {F : adjacentExtensions (K := K) d E.val // (1 : K) ∈ F.val} ≃
      adjacentExtensions (K := K) d E.val where
  toFun := Subtype.val
  invFun F := ⟨F, F.property.1 E.property.2⟩
  left_inv F := by
    apply Subtype.ext
    rfl
  right_inv F := rfl

set_option linter.style.haveILetI false in
/-- The quotient by a `d`-dimensional subspace of an `n`-dimensional binary
space has exactly `2^(n-d)` elements. This is the finite-vector-space input
for counting one-dimensional extensions of a fixed subspace. -/
theorem quotient_card_eq_pow (n d : ℕ) (E : Submodule (ZMod 2) K)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : Module.finrank (ZMod 2) E = d) :
    Nat.card (K ⧸ E) = 2 ^ (n - d) := by
  classical
  letI : Fintype (K ⧸ E) := Fintype.ofFinite _
  have hdim := E.finrank_quotient_add_finrank
  have hquot : Module.finrank (ZMod 2) (K ⧸ E) + d = n := by
    rw [hd, hn] at hdim
    exact hdim
  have htwo : Fintype.card (ZMod 2) = 2 := by decide
  have hexp : Module.finrank (ZMod 2) (K ⧸ E) = n - d := by omega
  calc
    Nat.card (K ⧸ E) = Fintype.card (K ⧸ E) := Nat.card_eq_fintype_card
    _ = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (K ⧸ E) :=
      Module.card_eq_pow_finrank
    _ = 2 ^ (n - d) := by rw [htwo, hexp]

set_option linter.style.haveILetI false in
theorem quotient_nonzero_card_eq_pow_sub_one (n d : ℕ)
    (E : Submodule (ZMod 2) K)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : Module.finrank (ZMod 2) E = d) :
    Nat.card {x : K ⧸ E // x ≠ 0} = 2 ^ (n - d) - 1 := by
  classical
  letI : Fintype (K ⧸ E) := Fintype.ofFinite _
  have hz : (0 : K ⧸ E) ∈ (Finset.univ : Finset (K ⧸ E)) := Finset.mem_univ _
  have hcard : Nat.card {x : K ⧸ E // x ≠ 0} =
      ((Finset.univ : Finset (K ⧸ E)).erase 0).card := by
    calc
      _ = Fintype.card {x : K ⧸ E // x ≠ 0} := Nat.card_eq_fintype_card
      _ = (Finset.univ.filter fun x : K ⧸ E => x ≠ 0).card := Fintype.card_subtype _
      _ = ((Finset.univ : Finset (K ⧸ E)).erase 0).card := by
        congr 1
        ext x
        simp [Finset.mem_erase]
  rw [hcard]
  have hsize : ((Finset.univ : Finset (K ⧸ E)).erase 0).card + 1 =
      2 ^ (n - d) := by
    rw [Finset.card_erase_add_one hz, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact quotient_card_eq_pow n d E hn hd
  omega

theorem quotient_binaryLines_card_eq_pow_sub_one (n d : ℕ)
    (E : Submodule (ZMod 2) K)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : Module.finrank (ZMod 2) E = d) :
    Nat.card (binaryLines (V := K ⧸ E)) = 2 ^ (n - d) - 1 := by
  calc
    Nat.card (binaryLines (V := K ⧸ E)) =
        Nat.card {x : K ⧸ E // x ≠ 0} :=
      Nat.card_congr (nonzeroVectorBinaryLineEquiv (V := K ⧸ E)).symm
    _ = 2 ^ (n - d) - 1 := quotient_nonzero_card_eq_pow_sub_one n d E hn hd

theorem adjacentExtensions_card_eq_pow_sub_one (n d : ℕ)
    (E : Submodule (ZMod 2) K)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : Module.finrank (ZMod 2) E = d) :
    Nat.card (adjacentExtensions (K := K) d E) = 2 ^ (n - d) - 1 := by
  calc
    Nat.card (adjacentExtensions (K := K) d E) =
        Nat.card (binaryLines (V := K ⧸ E)) :=
      Nat.card_congr (binaryLineAdjacentExtensionEquiv d E hd).symm
    _ = Nat.card {x : K ⧸ E // x ≠ 0} :=
      Nat.card_congr (nonzeroVectorBinaryLineEquiv (V := K ⧸ E)).symm
    _ = 2 ^ (n - d) - 1 := quotient_nonzero_card_eq_pow_sub_one n d E hn hd

theorem adjacentExtensionsContainingOne_card (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (E : dimensionFiberContainingOne (K := K) d) :
    Nat.card {F : adjacentExtensions (K := K) d E.val // (1 : K) ∈ F.val} =
      2 ^ (n - d) - 1 := by
  calc
    _ = Nat.card (adjacentExtensions (K := K) d E.val) :=
      Nat.card_congr (adjacentExtensionsContainingOneEquiv d E)
    _ = 2 ^ (n - d) - 1 :=
      adjacentExtensions_card_eq_pow_sub_one n d E.val hn E.property.1

theorem adjacentOneFlagsByLower_card (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) :
    Nat.card (adjacentOneFlagsByLower (K := K) d) =
      Nat.card (dimensionFiberContainingOne (K := K) d) *
        (2 ^ (n - d) - 1) := by
  classical
  calc
    _ = ∑ E : dimensionFiberContainingOne (K := K) d,
          Nat.card {F : adjacentExtensions (K := K) d E.val // (1 : K) ∈ F.val} :=
      Nat.card_sigma
    _ = ∑ _E : dimensionFiberContainingOne (K := K) d,
          (2 ^ (n - d) - 1) := by
      apply Finset.sum_congr rfl
      intro E hE
      exact adjacentExtensionsContainingOne_card n d hn E
    _ = Fintype.card (dimensionFiberContainingOne (K := K) d) *
          (2 ^ (n - d) - 1) := by simp [Finset.sum_const]
    _ = _ := by rw [Nat.card_eq_fintype_card]

theorem adjacentOneFlagsByUpper_card (d : ℕ) :
    Nat.card (adjacentOneFlagsByUpper (K := K) d) =
      Nat.card (dimensionFiberContainingOne (K := K) (d + 1)) *
        (2 ^ d - 1) := by
  classical
  calc
    _ = ∑ F : dimensionFiberContainingOne (K := K) (d + 1),
          Nat.card (subspacesBelowOne F.val d) := Nat.card_sigma
    _ = ∑ _F : dimensionFiberContainingOne (K := K) (d + 1),
          (2 ^ d - 1) := by
      apply Finset.sum_congr rfl
      intro F hF
      exact subspacesBelowOne_card_eq_pow_sub_one F.val d
        F.property.1 F.property.2
    _ = Fintype.card (dimensionFiberContainingOne (K := K) (d + 1)) *
          (2 ^ d - 1) := by simp [Finset.sum_const]
    _ = _ := by rw [Nat.card_eq_fintype_card]

theorem adjacentOneFlags_double_count (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) :
    Nat.card (dimensionFiberContainingOne (K := K) d) *
        (2 ^ (n - d) - 1) =
      Nat.card (dimensionFiberContainingOne (K := K) (d + 1)) *
        (2 ^ d - 1) := by
  calc
    _ = Nat.card (adjacentOneFlagsByLower (K := K) d) :=
      (adjacentOneFlagsByLower_card n d hn).symm
    _ = Nat.card (adjacentOneFlagsByUpper (K := K) d) := by
      calc
        _ = Nat.card (adjacentOneFlags (K := K) d) :=
          Nat.card_congr (adjacentOneFlagsEquivByLower d).symm
        _ = _ := Nat.card_congr (adjacentOneFlagsEquivByUpper d)
    _ = _ := adjacentOneFlagsByUpper_card d

#print axioms quotient_card_eq_pow
#print axioms quotient_nonzero_card_eq_pow_sub_one
#print axioms nonzeroVectorBinaryLineEquiv
#print axioms finrank_comap_binaryLine
#print axioms comap_span_mkQ_eq_sup
#print axioms finrank_comapMkQRelIso_symm_binaryLine
#print axioms binaryLineAdjacentExtensionEquiv
#print axioms adjacentExtensions_card_eq_pow_sub_one
#print axioms quotient_binaryLines_card_eq_pow_sub_one
#print axioms binaryDual_finrank_eq
#print axioms binaryDual_card_eq_pow
#print axioms binaryFunctional_ker_codim_one
#print axioms binaryHyperplane_quotient_finrank
#print axioms ker_binaryFunctionalOfHyperplane
#print axioms binaryFunctionalOfHyperplane_ne_zero
#print axioms binaryFunctionals_eq_of_ker_eq
#print axioms binaryHyperplaneFunctionalEquiv
#print axioms binaryHyperplaneContainingFunctionalEquiv
#print axioms binaryEvalAt_ne_zero
#print axioms binaryFunctionalsVanishingEquivKernelNonzero
#print axioms binarySubmoduleNonzero_card
#print axioms binaryHyperplanesContaining_card
#print axioms submodulesBelowEquiv
#print axioms finrank_comap_submoduleBelow
#print axioms subspacesBelowOneEquivHyperplanes
#print axioms subspacesBelowOne_card_eq_pow_sub_one
#print axioms adjacentExtensionsContainingOneEquiv
#print axioms adjacentExtensionsContainingOne_card
#print axioms adjacentOneFlagsEquivByLower
#print axioms adjacentOneFlagsEquivByUpper
#print axioms adjacentOneFlagsByLower_card
#print axioms adjacentOneFlagsByUpper_card
#print axioms adjacentOneFlags_double_count

end Carlet
