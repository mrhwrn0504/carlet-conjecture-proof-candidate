import Carlet.IncidenceCounting
import Carlet.TraceDuality
import Carlet.DualPolynomial

noncomputable section

open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

attribute [local instance] Classical.propDecidable

local instance distributionSubmoduleFinite : Finite (Submodule (ZMod 2) K) :=
  Finite.of_injective (fun E : Submodule (ZMod 2) K => (E : Set K)) SetLike.coe_injective

local instance distributionSubspaceFintype (E : Submodule (ZMod 2) K) : Fintype E :=
  Fintype.ofFinite E

local instance distributionCoefficientFiberFinite (d : ℕ) (x : K) :
    Finite (coefficientFiber (K := K) d x) :=
  Finite.of_injective (fun E : coefficientFiber (K := K) d x => E.val) Subtype.val_injective

local instance distributionCoefficientFiberFintype (d : ℕ) (x : K) :
    Fintype (coefficientFiber (K := K) d x) := Fintype.ofFinite _

def traceCoefficientFiber (d : ℕ) (x : K) : Type _ :=
  {E : coefficientFiber (K := K) d x //
    E.val ≤ LinearMap.ker (Algebra.trace (ZMod 2) K)}

local instance traceCoefficientFiberFinite (d : ℕ) (x : K) :
    Finite (traceCoefficientFiber (K := K) d x) :=
  Finite.of_injective (fun E : traceCoefficientFiber (K := K) d x => E.val)
    Subtype.val_injective

local instance traceCoefficientFiberFintype (d : ℕ) (x : K) :
    Fintype (traceCoefficientFiber (K := K) d x) := Fintype.ofFinite _

omit [DecidableEq K] in
set_option linter.style.haveILetI false in
theorem traceCharacter_weighted_fiber_sum (d : ℕ) (x : K) :
    (∑ E : coefficientFiber (K := K) d x,
      ∑ v : E.val, traceCharacter (K := K) (v : K)) =
      (2 ^ d : ℝ) * (Nat.card (traceCoefficientFiber (K := K) d x) : ℝ) := by
  classical
  let P : coefficientFiber (K := K) d x → Prop := fun E =>
    E.val ≤ LinearMap.ker (Algebra.trace (ZMod 2) K)
  let s : Finset (coefficientFiber (K := K) d x) := Finset.univ.filter P
  letI : Fintype {E : coefficientFiber (K := K) d x // P E} := Fintype.ofFinite _
  have hterms (E : coefficientFiber (K := K) d x) :
      (∑ v : E.val, traceCharacter (K := K) (v : K)) =
        if P E then (2 ^ d : ℝ) else 0 := by
    have horth := traceCharacter_sum_subspace (K := K) E.val
    have hcard : Nat.card E.val = 2 ^ d := by
      rw [← underlyingFinset_card, underlyingFinset_card_pow, E.property.1]
    rw [hcard] at horth
    simpa [P] using horth
  calc
    _ = ∑ E : coefficientFiber (K := K) d x, if P E then (2 ^ d : ℝ) else 0 := by
      apply Fintype.sum_congr
      intro E
      exact hterms E
    _ = ∑ E ∈ s, (2 ^ d : ℝ) := by
      simpa [s, P] using
        (Fintype.sum_ite_mem s (fun _ : coefficientFiber (K := K) d x => (2 ^ d : ℝ)))
    _ = (s.card : ℝ) * (2 ^ d : ℝ) := by simp
    _ = (Fintype.card {E : coefficientFiber (K := K) d x // P E} : ℝ) * (2 ^ d : ℝ) := by
      have hsubcard :
          Fintype.card {E : coefficientFiber (K := K) d x // P E} = s.card := by
        simpa [s, P] using (Fintype.card_subtype P)
      rw [← hsubcard]
    _ = _ := by
      have hcard : Nat.card {E : coefficientFiber (K := K) d x // P E} =
          Nat.card (traceCoefficientFiber (K := K) d x) := by
        rfl
      rw [← Nat.card_eq_fintype_card, hcard]
      ring

def traceSubspaceCoefficientFiber (d : ℕ) (x : K) : Type _ :=
  {V : {V : Submodule (ZMod 2) K //
      V ≤ LinearMap.ker (Algebra.trace (ZMod 2) K)} //
    Module.finrank (ZMod 2) V.val = d ∧ nextFrobeniusCoefficient V.val = x}

def traceCoefficientFiberEquiv (d : ℕ) (x : K) :
    traceSubspaceCoefficientFiber (K := K) d x ≃ traceCoefficientFiber (K := K) d x where
  toFun V := ⟨⟨V.val.val, V.property.1, V.property.2⟩, V.val.property⟩
  invFun E := ⟨⟨E.val.val, E.property⟩, E.val.property.1, E.val.property.2⟩
  left_inv V := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv E := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem artinSchreier_traceFiber_card (d : ℕ) (hd : 0 < d) (b : K) :
    Nat.card {H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H} //
      Module.finrank (ZMod 2) H.val = d+1 ∧ nextFrobeniusCoefficient H.val = b} =
      Nat.card (traceCoefficientFiber (K := K) d (b+1)) := by
  calc
    _ = Nat.card (traceSubspaceCoefficientFiber (K := K) d (b+1)) :=
      coefficientFiber_card d hd b
    _ = _ := Nat.card_congr (traceCoefficientFiberEquiv (K := K) d (b+1))

theorem artinSchreier_fiber_weighted_sum (d : ℕ) (hd : 0 < d) (b : K) :
    (2 ^ d : ℝ) * (Nat.card {H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H} //
      Module.finrank (ZMod 2) H.val = d+1 ∧ nextFrobeniusCoefficient H.val = b} : ℝ) =
      ∑ V : coefficientFiber (K := K) d (b+1),
        ∑ v : V.val, traceCharacter (K := K) (v : K) := by
  rw [artinSchreier_traceFiber_card d hd b]
  exact (traceCharacter_weighted_fiber_sum d (b+1)).symm

def fixedVectorCoefficientFiber (d : ℕ) (b : K) (v : {v : K // v ≠ 0}) : Type _ :=
  {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = d ∧
    nextFrobeniusCoefficient E = b ∧ v.val ∈ E}

def containingOneCoefficientFiber (d : ℕ) (c : K) : Type _ :=
  {H : Submodule (ZMod 2) K // Module.finrank (ZMod 2) H = d ∧
    (1 : K) ∈ H ∧ nextFrobeniusCoefficient H = c}

def fixedVectorScalingEquiv (d : ℕ) (hd : 0 < d) (b : K)
    (v : {v : K // v ≠ 0}) :
    fixedVectorCoefficientFiber (K := K) d b v ≃
      containingOneCoefficientFiber (K := K) d
        (((nonzeroValueUnit v : Kˣ)⁻¹ : K)^(2^(d-1)) * b) where
  toFun E := by
    let u := nonzeroValueUnit v
    let H := scalarSubspace E.val u⁻¹
    have hdim : Module.finrank (ZMod 2) H = d := by
      rw [scalarSubspace_finrank]
      exact E.property.1
    have h1 : (1 : K) ∈ H := by
      rw [mem_scalarSubspace]
      simpa [H, u, nonzeroValueUnit] using E.property.2.2
    have ht := nextCoefficient_scalarSubspace E.val u⁻¹ (by rw [E.property.1]; exact hd)
    rw [E.property.1, E.property.2.1] at ht
    exact ⟨H, hdim, h1, ht⟩
  invFun H := by
    let u := nonzeroValueUnit v
    let E := scalarSubspace H.val u
    have hdim : Module.finrank (ZMod 2) E = d := by
      rw [scalarSubspace_finrank]
      exact H.property.1
    have hv : v.val ∈ E := by
      rw [mem_scalarSubspace]
      have hcancel : (u : K)⁻¹ * v.val = 1 := by
        dsimp [u, nonzeroValueUnit]
        field_simp [v.property]
      rw [hcancel]
      exact H.property.2.1
    have ht := nextCoefficient_scalarSubspace H.val u (by rw [H.property.1]; exact hd)
    rw [H.property.1, H.property.2.2] at ht
    have hpow : (u : K)^(2^(d-1)) * ((u : K)⁻¹)^(2^(d-1)) = 1 := by
      rw [← mul_pow]
      simp
    change nextFrobeniusCoefficient (scalarSubspace H.val u) =
      (u : K)^(2^(d-1)) * (((u : K)⁻¹)^(2^(d-1)) * b) at ht
    rw [← mul_assoc, hpow, one_mul] at ht
    exact ⟨E, hdim, ht, hv⟩
  left_inv E := by
    let u := nonzeroValueUnit v
    apply Subtype.ext
    exact (scalarSubspaceEquiv u).right_inv E.val
  right_inv H := by
    let u := nonzeroValueUnit v
    apply Subtype.ext
    exact (scalarSubspaceEquiv u).left_inv H.val

omit [DecidableEq K] in
theorem fixedVectorCoefficientFiber_card (d : ℕ) (hd : 0 < d) (b : K)
    (v : {v : K // v ≠ 0}) :
    Nat.card (fixedVectorCoefficientFiber (K := K) d b v) =
      Nat.card (containingOneCoefficientFiber (K := K) d
        (((nonzeroValueUnit v : Kˣ)⁻¹ : K)^(2^(d-1)) * b)) :=
  Nat.card_congr (fixedVectorScalingEquiv (K := K) d hd b v)

def containingOneCoefficientFiberNestedEquiv (d : ℕ) (c : K) :
    containingOneCoefficientFiber (K := K) d c ≃
      {H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H} //
        Module.finrank (ZMod 2) H.val = d ∧ nextFrobeniusCoefficient H.val = c} where
  toFun H := ⟨⟨H.val, H.property.2.1⟩, H.property.1, H.property.2.2⟩
  invFun H := ⟨H.val.val, H.property.1, H.val.property, H.property.2⟩
  left_inv H := by
    apply Subtype.ext
    rfl
  right_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem containingOneCoefficientFiber_trace_card (d : ℕ) (hd : 0 < d) (b : K) :
    Nat.card (containingOneCoefficientFiber (K := K) (d+1) b) =
      Nat.card (traceCoefficientFiber (K := K) d (b+1)) := by
  calc
    _ = Nat.card {H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H} //
          Module.finrank (ZMod 2) H.val = d+1 ∧ nextFrobeniusCoefficient H.val = b} :=
      Nat.card_congr (containingOneCoefficientFiberNestedEquiv (K := K) (d+1) b)
    _ = Nat.card (traceSubspaceCoefficientFiber (K := K) d (b+1)) :=
      coefficientFiber_card d hd b
    _ = _ := Nat.card_congr (traceCoefficientFiberEquiv (K := K) d (b+1))

theorem containingOne_fiber_weighted_sum (d : ℕ) (hd : 0 < d) (b : K) :
    (2 ^ d : ℝ) * (Nat.card (containingOneCoefficientFiber (K := K) (d+1) b) : ℝ) =
      ∑ V : coefficientFiber (K := K) d (b+1),
        ∑ v : V.val, traceCharacter (K := K) (v : K) := by
  rw [containingOneCoefficientFiber_trace_card d hd b]
  exact (traceCharacter_weighted_fiber_sum d (b+1)).symm

def coefficientFiberContainingVector (d : ℕ) (x v : K) : Type _ :=
  {E : coefficientFiber (K := K) d x // v ∈ E.val}

def coefficientFiberContainingZeroEquiv (d : ℕ) (x : K) :
    coefficientFiber (K := K) d x ≃ coefficientFiberContainingVector (K := K) d x 0 where
  toFun E := ⟨E, Submodule.zero_mem E.val⟩
  invFun E := E.val
  left_inv _ := rfl
  right_inv E := by
    apply Subtype.ext
    rfl

def coefficientFiberContainingVectorEquiv (d : ℕ) (x : K) (v : {v : K // v ≠ 0}) :
    coefficientFiberContainingVector (K := K) d x v.val ≃
      fixedVectorCoefficientFiber (K := K) d x v where
  toFun E := ⟨E.val.val, E.val.property.1, E.val.property.2, E.property⟩
  invFun E := ⟨⟨E.val, E.property.1, E.property.2.1⟩, E.property.2.2⟩
  left_inv E := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv E := by
    apply Subtype.ext
    rfl

local instance coefficientFiberContainingVectorFinite (d : ℕ) (x v : K) :
    Finite (coefficientFiberContainingVector (K := K) d x v) :=
  Finite.of_injective (fun E : coefficientFiberContainingVector (K := K) d x v => E.val)
    Subtype.val_injective

local instance coefficientFiberContainingVectorFintype (d : ℕ) (x v : K) :
    Fintype (coefficientFiberContainingVector (K := K) d x v) := Fintype.ofFinite _

local instance distributionNonzeroFinite : Finite {v : K // v ≠ 0} :=
  Finite.of_injective (fun v : {v : K // v ≠ 0} => v.val) Subtype.val_injective

local instance distributionNonzeroFintype : Fintype {v : K // v ≠ 0} := Fintype.ofFinite _

omit [DecidableEq K] in
set_option linter.style.haveILetI false in
theorem coefficientFiber_membership_character_sum (d : ℕ) (x v : K) :
    (∑ E : coefficientFiber (K := K) d x,
      if v ∈ E.val then traceCharacter (K := K) v else 0) =
      traceCharacter (K := K) v *
        (Nat.card (coefficientFiberContainingVector (K := K) d x v) : ℝ) := by
  classical
  let P : coefficientFiber (K := K) d x → Prop := fun E => v ∈ E.val
  let s : Finset (coefficientFiber (K := K) d x) := Finset.univ.filter P
  letI : Fintype {E : coefficientFiber (K := K) d x // P E} := Fintype.ofFinite _
  have hsubcard : Fintype.card {E : coefficientFiber (K := K) d x // P E} = s.card := by
    simpa [s, P] using (Fintype.card_subtype P)
  calc
    _ = ∑ E ∈ s, traceCharacter (K := K) v := by
      simpa [s, P] using
        (Fintype.sum_ite_mem s (fun _ : coefficientFiber (K := K) d x =>
          traceCharacter (K := K) v))
    _ = (s.card : ℝ) * traceCharacter (K := K) v := by simp
    _ = (Fintype.card {E : coefficientFiber (K := K) d x // P E} : ℝ) *
          traceCharacter (K := K) v := by rw [← hsubcard]
    _ = _ := by
      have hcard : Nat.card {E : coefficientFiber (K := K) d x // P E} =
          Nat.card (coefficientFiberContainingVector (K := K) d x v) := by rfl
      rw [← Nat.card_eq_fintype_card]
      rw [hcard]
      ring

theorem coefficientFiber_subspace_character_sum (d : ℕ) (x : K) :
    (∑ E : coefficientFiber (K := K) d x,
      ∑ v : E.val, traceCharacter (K := K) (v : K)) =
      ∑ v : K, traceCharacter (K := K) v *
        (Nat.card (coefficientFiberContainingVector (K := K) d x v) : ℝ) := by
  classical
  have hinner (E : coefficientFiber (K := K) d x) :
      (∑ v : E.val, traceCharacter (K := K) (v : K)) =
        ∑ v : K, if v ∈ E.val then traceCharacter (K := K) v else 0 := by
    calc
      _ = ∑ v ∈ underlyingFinset E.val, traceCharacter (K := K) v :=
        (Finset.sum_subtype (underlyingFinset E.val) (mem_underlyingFinset E.val)
          (traceCharacter (K := K))).symm
      _ = _ := by
        simpa only [mem_underlyingFinset] using
          (Fintype.sum_ite_mem (underlyingFinset E.val)
            (fun v : K => traceCharacter (K := K) v)).symm
  calc
    _ = ∑ E : coefficientFiber (K := K) d x,
          ∑ v : K, if v ∈ E.val then traceCharacter (K := K) v else 0 := by
      apply Fintype.sum_congr
      intro E
      exact hinner E
    _ = ∑ v : K, ∑ E : coefficientFiber (K := K) d x,
          if v ∈ E.val then traceCharacter (K := K) v else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Fintype.sum_congr
      intro v
      exact coefficientFiber_membership_character_sum d x v

theorem coefficientFiberContainingVector_card_spec (d : ℕ) (hd : 0 < d) (x v : K) :
    Nat.card (coefficientFiberContainingVector (K := K) d x v) =
      if hv : v = 0 then Nat.card (coefficientFiber (K := K) d x) else
        Nat.card (containingOneCoefficientFiber (K := K) d
          (((nonzeroValueUnit ⟨v, hv⟩ : Kˣ)⁻¹ : K)^(2^(d-1)) * x)) := by
  by_cases hv : v = 0
  · subst v
    simpa using (Nat.card_congr (coefficientFiberContainingZeroEquiv (K := K) d x)).symm
  · let w : {v : K // v ≠ 0} := ⟨v, hv⟩
    have he := coefficientFiberContainingVectorEquiv (K := K) d x w
    have hc := fixedVectorCoefficientFiber_card (K := K) d hd x w
    simpa [hv, w] using (Nat.card_congr he).trans hc

def nonzeroIncidenceTerm (d : ℕ) (x v : K) : ℝ :=
  if hv : v = 0 then 0 else
    traceCharacter (K := K) v *
      (Nat.card (containingOneCoefficientFiber (K := K) d
        (((nonzeroValueUnit ⟨v, hv⟩ : Kˣ)⁻¹ : K)^(2^(d-1)) * x)) : ℝ)

theorem artinSchreier_character_count_recursion (d : ℕ) (hd : 0 < d) (b : K) :
    (2 ^ d : ℝ) * (Nat.card (containingOneCoefficientFiber (K := K) (d+1) b) : ℝ) =
      (Nat.card (coefficientFiber (K := K) d (b+1)) : ℝ) +
        ∑ v : K, nonzeroIncidenceTerm (K := K) d (b+1) v := by
  classical
  let x := b+1
  calc
    _ = ∑ V : coefficientFiber (K := K) d x,
          ∑ v : V.val, traceCharacter (K := K) (v : K) := by
      simpa [x] using containingOne_fiber_weighted_sum (K := K) d hd b
    _ = ∑ v : K, traceCharacter (K := K) v *
          (Nat.card (coefficientFiberContainingVector (K := K) d x v) : ℝ) :=
      coefficientFiber_subspace_character_sum (K := K) d x
    _ = _ := by
      have hpoint (v : K) :
          traceCharacter (K := K) v *
              (Nat.card (coefficientFiberContainingVector (K := K) d x v) : ℝ) =
            (if v = 0 then (Nat.card (coefficientFiber (K := K) d x) : ℝ) else 0) +
              nonzeroIncidenceTerm (K := K) d x v := by
        rw [coefficientFiberContainingVector_card_spec d hd x v]
        by_cases hv : v = 0
        · subst v
          simp [nonzeroIncidenceTerm, traceCharacter]
        · simp [nonzeroIncidenceTerm, hv]
      calc
        _ = ∑ v : K,
              ((if v = 0 then (Nat.card (coefficientFiber (K := K) d x) : ℝ) else 0) +
                nonzeroIncidenceTerm (K := K) d x v) := by
          apply Fintype.sum_congr
          intro v
          exact hpoint v
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp [x, Nat.card_eq_fintype_card]

def frobeniusPowerEquiv (n : ℕ) : K ≃ K := by
  have hinj : Function.Injective (fun x : K => x^(2^n)) := by
    have h := ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K)^n).injective
    simpa only [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] using h
  exact Equiv.ofBijective _ ⟨hinj, pow_two_surjective n⟩

def nonzeroFrobeniusPowerEquiv (n : ℕ) : {v : K // v ≠ 0} ≃ {v : K // v ≠ 0} :=
  (frobeniusPowerEquiv (K := K) n).subtypeEquiv (fun v => by
    change v ≠ 0 ↔ v^(2^n) ≠ 0
    constructor
    · exact pow_ne_zero _
    · intro h
      by_contra hv
      subst v
      simp at h)

omit [DecidableEq K] in
theorem traceCharacter_frobeniusPower (v : K) (n : ℕ) :
    traceCharacter (K := K) (v^(2^n)) = traceCharacter (K := K) v := by
  change binaryCharacter (Algebra.trace (ZMod 2) K (v^(2^n))) = _
  exact congrArg binaryCharacter (trace_pow_two v n)

def scaledFiberCharacterTerm (d : ℕ) (x : K) (v : {v : K // v ≠ 0}) : ℝ :=
  traceCharacter (K := K) v.val *
    (Nat.card (containingOneCoefficientFiber (K := K) d
      (((nonzeroValueUnit v : Kˣ)⁻¹ : K)^(2^(d-1)) * x)) : ℝ)

def reciprocalFiberCharacterTerm (d : ℕ) (x : K) (w : {w : K // w ≠ 0}) : ℝ :=
  traceCharacter (K := K) w.val *
    (Nat.card (containingOneCoefficientFiber (K := K) d (x / w.val)) : ℝ)

omit [DecidableEq K] in
theorem nonzero_frobenius_reindex (d : ℕ) (x : K) :
    (∑ v : {v : K // v ≠ 0}, scaledFiberCharacterTerm (K := K) d x v) =
      ∑ w : {w : K // w ≠ 0}, reciprocalFiberCharacterTerm (K := K) d x w := by
  classical
  apply Fintype.sum_equiv (nonzeroFrobeniusPowerEquiv (K := K) (d-1))
    (fun v => scaledFiberCharacterTerm (K := K) d x v)
    (fun w => reciprocalFiberCharacterTerm (K := K) d x w)
  intro v
  have hψ := traceCharacter_frobeniusPower (K := K) v.val (d-1)
  have harg :
      (((nonzeroValueUnit v : Kˣ)⁻¹ : K)^(2^(d-1)) * x) =
        x / (v.val^(2^(d-1))) := by
    change (v.val⁻¹)^(2^(d-1)) * x = x / (v.val^(2^(d-1)))
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  simp only [scaledFiberCharacterTerm, reciprocalFiberCharacterTerm]
  have hval : ((nonzeroFrobeniusPowerEquiv (K := K) (d-1)) v).val =
      v.val^(2^(d-1)) := rfl
  rw [hval, hψ, harg]

theorem nonzeroIncidence_sum_reindex (d : ℕ) (x : K) :
    (∑ v : K, nonzeroIncidenceTerm (K := K) d x v) =
      ∑ w : {w : K // w ≠ 0}, reciprocalFiberCharacterTerm (K := K) d x w := by
  classical
  have hzero : nonzeroIncidenceTerm (K := K) d x 0 = 0 := by
    simp [nonzeroIncidenceTerm]
  have herase := Finset.sum_erase_add (Finset.univ : Finset K)
    (fun v => nonzeroIncidenceTerm (K := K) d x v) (Finset.mem_univ 0)
  calc
    _ = ∑ v ∈ (Finset.univ : Finset K).erase 0, nonzeroIncidenceTerm (K := K) d x v := by
      rw [hzero] at herase
      rw [add_zero] at herase
      exact herase.symm
    _ = ∑ v : {v : K // v ≠ 0}, nonzeroIncidenceTerm (K := K) d x v.val :=
      Finset.sum_subtype ((Finset.univ : Finset K).erase 0)
        (by intro v; simp [Finset.mem_erase])
        (fun v => nonzeroIncidenceTerm (K := K) d x v)
    _ = ∑ v : {v : K // v ≠ 0}, scaledFiberCharacterTerm (K := K) d x v := by
      apply Fintype.sum_congr
      intro v
      simp [nonzeroIncidenceTerm, scaledFiberCharacterTerm, v.property]
    _ = _ := nonzero_frobenius_reindex (K := K) d x

theorem artinSchreier_character_count_recursion_reindexed
    (d : ℕ) (hd : 0 < d) (b : K) :
    (2 ^ d : ℝ) * (Nat.card (containingOneCoefficientFiber (K := K) (d+1) b) : ℝ) =
      (Nat.card (coefficientFiber (K := K) d (b+1)) : ℝ) +
        ∑ w : {w : K // w ≠ 0}, reciprocalFiberCharacterTerm (K := K) d (b+1) w := by
  calc
    _ = (Nat.card (coefficientFiber (K := K) d (b+1)) : ℝ) +
          ∑ v : K, nonzeroIncidenceTerm (K := K) d (b+1) v :=
      artinSchreier_character_count_recursion (K := K) d hd b
    _ = _ := by rw [nonzeroIncidence_sum_reindex]

#print axioms traceCharacter_weighted_fiber_sum
#print axioms artinSchreier_fiber_weighted_sum
#print axioms fixedVectorScalingEquiv
#print axioms coefficientFiber_subspace_character_sum
#print axioms artinSchreier_character_count_recursion
#print axioms frobeniusPowerEquiv
#print axioms traceCharacter_frobeniusPower
#print axioms nonzero_frobenius_reindex
#print axioms artinSchreier_character_count_recursion_reindexed

end Carlet
