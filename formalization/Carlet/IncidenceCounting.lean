import Carlet.CoefficientScaling

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance submoduleFinite : Finite (Submodule (ZMod 2) K) :=
  Finite.of_injective (fun E : Submodule (ZMod 2) K => (E : Set K)) SetLike.coe_injective

def zeroCoefficientFiber (k : ℕ) : Type _ := coefficientFiber (K := K) k (0 : K)

def zeroCoefficientFiberContainingOne (k : ℕ) : Type _ :=
  {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧
    (1 : K) ∈ E ∧ nextFrobeniusCoefficient E = 0}

def markedZeroSubspacePairs (k : ℕ) : Type _ :=
  {p : zeroCoefficientFiber (K := K) k × K // p.2 ∈ p.1.val ∧ p.2 ≠ 0}

def markedZeroSigmaPairs (k : ℕ) : Type _ :=
  Σ E : zeroCoefficientFiber (K := K) k, {v : K // v ∈ E.val ∧ v ≠ 0}

local instance zeroCoefficientFiberFinite (k : ℕ) :
    Finite (zeroCoefficientFiber (K := K) k) :=
  Finite.of_injective (fun E : zeroCoefficientFiber (K := K) k => E.val) Subtype.val_injective

local instance zeroCoefficientFiberFintype (k : ℕ) :
    Fintype (zeroCoefficientFiber (K := K) k) := Fintype.ofFinite _

local instance markedZeroFiberFinite (k : ℕ) (E : zeroCoefficientFiber (K := K) k) :
    Finite {v : K // v ∈ E.val ∧ v ≠ 0} :=
  Finite.of_injective (fun v : {v : K // v ∈ E.val ∧ v ≠ 0} => v.val)
    Subtype.val_injective

def dimensionFiber (k : ℕ) : Type _ :=
  {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k}

local instance dimensionFiberFinite (k : ℕ) : Finite (dimensionFiber (K := K) k) :=
  Finite.of_injective (fun E : dimensionFiber (K := K) k => E.val) Subtype.val_injective

local instance dimensionFiberFintype (k : ℕ) : Fintype (dimensionFiber (K := K) k) :=
  Fintype.ofFinite _

def dimensionFiberContainingOne (k : ℕ) : Type _ :=
  {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧ (1 : K) ∈ E}

local instance dimensionFiberContainingOneFinite (k : ℕ) :
    Finite (dimensionFiberContainingOne (K := K) k) :=
  Finite.of_injective (fun E : dimensionFiberContainingOne (K := K) k => E.val)
    Subtype.val_injective

def markedDimensionPairs (k : ℕ) : Type _ :=
  {p : dimensionFiber (K := K) k × K // p.2 ∈ p.1.val ∧ p.2 ≠ 0}

def markedDimensionSigmaPairs (k : ℕ) : Type _ :=
  Σ E : dimensionFiber (K := K) k, {v : K // v ∈ E.val ∧ v ≠ 0}

local instance dimensionMembersFinite (k : ℕ) (E : dimensionFiber (K := K) k) :
    Finite {v : K // v ∈ E.val ∧ v ≠ 0} :=
  Finite.of_injective (fun v : {v : K // v ∈ E.val ∧ v ≠ 0} => v.val)
    Subtype.val_injective

def markedDimensionPairsSigmaEquiv (k : ℕ) :
    markedDimensionPairs (K := K) k ≃ markedDimensionSigmaPairs (K := K) k where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨E, ⟨v, hv⟩⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl

def markedDimensionContainingOnePairs (k : ℕ) : Type _ :=
  {v : K // v ≠ 0} × dimensionFiberContainingOne (K := K) k

local instance coefficientFiberFinite (k : ℕ) (b : K) : Finite (coefficientFiber (K := K) k b) :=
  Finite.of_injective (fun E : coefficientFiber (K := K) k b => E.val) Subtype.val_injective

def coefficientFibersEquivDimension (k : ℕ) :
    (Σ b : K, coefficientFiber (K := K) k b) ≃ dimensionFiber (K := K) k where
  toFun p := ⟨p.2.val, p.2.property.1⟩
  invFun E := ⟨nextFrobeniusCoefficient E.val, ⟨E.val, E.property, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨b, ⟨E, hr, ht⟩⟩
    apply Sigma.ext ht
    cases ht
    rfl
  right_inv E := by
    apply Subtype.ext
    rfl

omit [DecidableEq K] in
theorem coefficientFibers_sum_card (k : ℕ) :
    (∑ b : K, Nat.card (coefficientFiber (K := K) k b)) =
      Nat.card (dimensionFiber (K := K) k) := by
  classical
  calc
    _ = Nat.card (Σ b : K, coefficientFiber (K := K) k b) := Nat.card_sigma.symm
    _ = Nat.card (dimensionFiber (K := K) k) :=
      Nat.card_congr (coefficientFibersEquivDimension (K := K) k)

theorem dimensionFiber_card_decomposition (k : ℕ) (hk : 0 < k) (b : K) (hb : b ≠ 0) :
    Nat.card (dimensionFiber (K := K) k) =
      Nat.card (zeroCoefficientFiber (K := K) k) +
        (Fintype.card K - 1) * Nat.card (coefficientFiber (K := K) k b) := by
  classical
  let f : K → ℕ := fun x => Nat.card (coefficientFiber (K := K) k x)
  have hparts : (∑ x ∈ (Finset.univ : Finset K).erase 0, f x) =
      ((Finset.univ : Finset K).erase 0).card * f b := by
    calc
      _ = ∑ x ∈ (Finset.univ : Finset K).erase 0, f b := by
        apply Finset.sum_congr rfl
        intro x hx
        exact coefficientFiber_card_eq_of_nonzero k hk x b
          (Finset.mem_erase.mp hx).1 hb
      _ = _ := by simp [Finset.sum_const]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset K) f (Finset.mem_univ 0)
  have hcard : ((Finset.univ : Finset K).erase 0).card + 1 = Fintype.card K :=
    Finset.card_erase_add_one (Finset.mem_univ 0)
  rw [← coefficientFibers_sum_card, ← hsum, hparts]
  have hzero : f 0 = Nat.card (zeroCoefficientFiber (K := K) k) := rfl
  rw [hzero]
  have hcard' : ((Finset.univ : Finset K).erase 0).card = Fintype.card K - 1 := by omega
  rw [hcard']
  ring

def markedZeroPairsSigmaEquiv (k : ℕ) :
    markedZeroSubspacePairs (K := K) k ≃ markedZeroSigmaPairs (K := K) k where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv p := by
    apply Subtype.ext
    rfl

  right_inv p := by
    rcases p with ⟨E, ⟨v, hv⟩⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl

def markedOneSubspacePairs (k : ℕ) : Type _ :=
  {v : K // v ≠ 0} × zeroCoefficientFiberContainingOne (K := K) k

def nonzeroSubspaceMembers (E : Submodule (ZMod 2) K) :=
  {v : K // v ∈ E ∧ v ≠ 0}

theorem nonzeroSubspaceMembers_card (E : Submodule (ZMod 2) K) (k : ℕ)
    (hk : Module.finrank (ZMod 2) E = k) :
    Nat.card {v : K // v ∈ E ∧ v ≠ 0} = 2 ^ k - 1 := by
  classical
  have hz : 0 ∈ underlyingFinset E := by simp
  have hcard : Nat.card {v : K // v ∈ E ∧ v ≠ 0} =
      ((underlyingFinset E).erase 0).card := by
    calc
      _ = Fintype.card {v : K // v ∈ E ∧ v ≠ 0} := Nat.card_eq_fintype_card
      _ = (Finset.univ.filter fun v : K => v ∈ E ∧ v ≠ 0).card :=
        Fintype.card_subtype _
      _ = ((underlyingFinset E).erase 0).card := by
        congr 1
        ext v
        simp [underlyingFinset, Finset.mem_erase, and_comm]
  rw [hcard]
  have he : ((underlyingFinset E).erase 0).card + 1 = 2 ^ k := by
    rw [Finset.card_erase_add_one hz, underlyingFinset_card_pow, hk]
  omega

omit [Algebra (ZMod 2) K] in
theorem nonzeroValues_card : Nat.card {v : K // v ≠ 0} = Fintype.card K - 1 := by
  classical
  have hz : 0 ∈ (Finset.univ : Finset K) := Finset.mem_univ 0
  have hcard : Nat.card {v : K // v ≠ 0} = ((Finset.univ : Finset K).erase 0).card := by
    calc
      _ = Fintype.card {v : K // v ≠ 0} := Nat.card_eq_fintype_card
      _ = ((Finset.univ : Finset K).filter fun v : K => v ≠ 0).card :=
        Fintype.card_subtype _
      _ = ((Finset.univ : Finset K).erase 0).card := by
        congr 1
        ext v
        simp [Finset.mem_erase]
  rw [hcard]
  have he : ((Finset.univ : Finset K).erase 0).card + 1 = Fintype.card K := by
    rw [Finset.card_erase_add_one hz]
    simp
  omega

def nonzeroValueUnit (v : {v : K // v ≠ 0}) : Kˣ := Units.mk0 v.val v.property

def markedZeroPairToOne (k : ℕ) (hk : 0 < k) :
    markedZeroSubspacePairs (K := K) k → markedOneSubspacePairs (K := K) k := fun p => by
  let u := nonzeroValueUnit ⟨p.val.2, p.property.2⟩
  let H := scalarSubspace p.val.1.val u⁻¹
  have hdim : Module.finrank (ZMod 2) H = k := by
    rw [scalarSubspace_finrank]
    exact p.val.1.property.1
  have h1 : (1 : K) ∈ H := by
    rw [mem_scalarSubspace]
    simpa [H, u, nonzeroValueUnit] using p.property.1
  have hτ : nextFrobeniusCoefficient H = 0 := by
    have hpos : 0 < Module.finrank (ZMod 2) p.val.1.val := by
      rw [p.val.1.property.1]
      exact hk
    exact (nextCoefficient_zero_scalarSubspace_iff p.val.1.val u⁻¹ hpos).mpr p.val.1.property.2
  exact (⟨p.val.2, p.property.2⟩, ⟨H, hdim, h1, hτ⟩)

def markedOnePairToZero (k : ℕ) (hk : 0 < k) :
    markedOneSubspacePairs (K := K) k → markedZeroSubspacePairs (K := K) k := fun p => by
  let u := nonzeroValueUnit p.1
  let E := scalarSubspace p.2.val u
  have hdim : Module.finrank (ZMod 2) E = k := by
    rw [scalarSubspace_finrank]
    exact p.2.property.1
  have hτ : nextFrobeniusCoefficient E = 0 := by
    exact (nextCoefficient_zero_scalarSubspace_iff p.2.val u
      (by rw [p.2.property.1]; exact hk)).mpr p.2.property.2.2
  have hv : p.1.val ∈ E := by
    rw [mem_scalarSubspace]
    have hcancel : (u : K)⁻¹ * p.1.val = 1 := by
      dsimp [u, nonzeroValueUnit]
      field_simp [p.1.property]
    rw [hcancel]
    exact p.2.property.2.1
  exact ⟨(⟨E, hdim, hτ⟩, p.1.val), hv, p.1.property⟩

def markedDimensionPairToContainingOne (k : ℕ) :
    markedDimensionPairs (K := K) k → markedDimensionContainingOnePairs (K := K) k :=
  fun p => by
    let u := nonzeroValueUnit ⟨p.val.2, p.property.2⟩
    let H := scalarSubspace p.val.1.val u⁻¹
    have hdim : Module.finrank (ZMod 2) H = k := by
      rw [scalarSubspace_finrank]
      exact p.val.1.property
    have h1 : (1 : K) ∈ H := by
      rw [mem_scalarSubspace]
      simpa [H, u, nonzeroValueUnit] using p.property.1
    exact (⟨p.val.2, p.property.2⟩, ⟨H, hdim, h1⟩)

def markedContainingOnePairToDimension (k : ℕ) :
    markedDimensionContainingOnePairs (K := K) k → markedDimensionPairs (K := K) k :=
  fun p => by
    let u := nonzeroValueUnit p.1
    let E := scalarSubspace p.2.val u
    have hdim : Module.finrank (ZMod 2) E = k := by
      rw [scalarSubspace_finrank]
      exact p.2.property.1
    have hv : p.1.val ∈ E := by
      rw [mem_scalarSubspace]
      have hcancel : (u : K)⁻¹ * p.1.val = 1 := by
        dsimp [u, nonzeroValueUnit]
        field_simp [p.1.property]
      rw [hcancel]
      exact p.2.property.2
    exact ⟨(⟨E, hdim⟩, p.1.val), hv, p.1.property⟩

def markedDimensionPairsEquivContainingOne (k : ℕ) :
    markedDimensionPairs (K := K) k ≃ markedDimensionContainingOnePairs (K := K) k where
  toFun := markedDimensionPairToContainingOne k
  invFun := markedContainingOnePairToDimension k
  left_inv p := by
    rcases p with ⟨⟨E, v⟩, hv, hv0⟩
    let u := nonzeroValueUnit ⟨v, hv0⟩
    have hfirst :
        (markedContainingOnePairToDimension k
          (markedDimensionPairToContainingOne k ⟨(E, v), hv, hv0⟩)).1.1 = E := by
      apply Subtype.ext
      change scalarSubspace (scalarSubspace E.val u⁻¹) u = E.val
      exact (scalarSubspaceEquiv u).right_inv E.val
    apply Subtype.ext
    apply Prod.ext
    · exact hfirst
    · rfl
  right_inv p := by
    rcases p with ⟨⟨v, hv0⟩, H⟩
    let u := nonzeroValueUnit ⟨v, hv0⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change scalarSubspace (scalarSubspace H.val u) u⁻¹ = H.val
      exact (scalarSubspaceEquiv u).left_inv H.val

def markedZeroSubspaceEquivOne (k : ℕ) (hk : 0 < k) :
    markedZeroSubspacePairs (K := K) k ≃ markedOneSubspacePairs (K := K) k where
  toFun := markedZeroPairToOne k hk
  invFun := markedOnePairToZero k hk
  left_inv p := by
    rcases p with ⟨⟨E, v⟩, hv, hv0⟩
    let u := nonzeroValueUnit ⟨v, hv0⟩
    have hfirst : (markedOnePairToZero k hk (markedZeroPairToOne k hk ⟨(E, v), hv, hv0⟩)).1.1 = E := by
      apply Subtype.ext
      change scalarSubspace (scalarSubspace E.val u⁻¹) u = E.val
      exact (scalarSubspaceEquiv u).right_inv E.val
    apply Subtype.ext
    apply Prod.ext
    · exact hfirst
    · rfl
  right_inv p := by
    rcases p with ⟨⟨v, hv0⟩, H⟩
    let u := nonzeroValueUnit ⟨v, hv0⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change scalarSubspace (scalarSubspace H.val u) u⁻¹ = H.val
      exact (scalarSubspaceEquiv u).left_inv H.val

omit [DecidableEq K] in
theorem markedZeroSubspacePairs_card_eq (k : ℕ) (hk : 0 < k) :
    Nat.card (markedZeroSubspacePairs (K := K) k) =
      Nat.card (markedOneSubspacePairs (K := K) k) :=
  Nat.card_congr (markedZeroSubspaceEquivOne (K := K) k hk)

theorem markedZeroSubspacePairs_card (k : ℕ) :
    Nat.card (markedZeroSubspacePairs (K := K) k) =
      Nat.card (zeroCoefficientFiber (K := K) k) * (2 ^ k - 1) := by
  classical
  calc
    _ = Nat.card (markedZeroSigmaPairs (K := K) k) :=
      Nat.card_congr (markedZeroPairsSigmaEquiv (K := K) k)
    _ = ∑ E : zeroCoefficientFiber (K := K) k,
          Nat.card {v : K // v ∈ E.val ∧ v ≠ 0} := Nat.card_sigma
    _ = ∑ _E : zeroCoefficientFiber (K := K) k, (2 ^ k - 1) := by
      apply Finset.sum_congr rfl
      intro E hE
      exact nonzeroSubspaceMembers_card E.val k E.property.1
    _ = Fintype.card (zeroCoefficientFiber (K := K) k) * (2 ^ k - 1) := by
      simp [Finset.sum_const]
    _ = _ := by rw [Nat.card_eq_fintype_card]

theorem markedOneSubspacePairs_card (k : ℕ) :
    Nat.card (markedOneSubspacePairs (K := K) k) =
      (Fintype.card K - 1) * Nat.card (zeroCoefficientFiberContainingOne (K := K) k) := by
  rw [markedOneSubspacePairs, Nat.card_prod, nonzeroValues_card]

theorem zeroCoefficient_incidence_count (k : ℕ) (hk : 0 < k) :
    Nat.card (zeroCoefficientFiber (K := K) k) * (2 ^ k - 1) =
      (Fintype.card K - 1) *
        Nat.card (zeroCoefficientFiberContainingOne (K := K) k) := by
  calc
    _ = Nat.card (markedZeroSubspacePairs (K := K) k) :=
      (markedZeroSubspacePairs_card (K := K) k).symm
    _ = Nat.card (markedOneSubspacePairs (K := K) k) :=
      markedZeroSubspacePairs_card_eq (K := K) k hk
    _ = _ := markedOneSubspacePairs_card (K := K) k

theorem markedDimensionPairs_card (k : ℕ) :
    Nat.card (markedDimensionPairs (K := K) k) =
      Nat.card (dimensionFiber (K := K) k) * (2 ^ k - 1) := by
  classical
  calc
    _ = Nat.card (markedDimensionSigmaPairs (K := K) k) :=
      Nat.card_congr (markedDimensionPairsSigmaEquiv (K := K) k)
    _ = ∑ E : dimensionFiber (K := K) k,
          Nat.card {v : K // v ∈ E.val ∧ v ≠ 0} := Nat.card_sigma
    _ = ∑ _E : dimensionFiber (K := K) k, (2 ^ k - 1) := by
      apply Finset.sum_congr rfl
      intro E hE
      exact nonzeroSubspaceMembers_card E.val k E.property
    _ = Fintype.card (dimensionFiber (K := K) k) * (2 ^ k - 1) := by
      simp [Finset.sum_const]
    _ = _ := by rw [Nat.card_eq_fintype_card]

theorem markedDimensionContainingOnePairs_card (k : ℕ) :
    Nat.card (markedDimensionContainingOnePairs (K := K) k) =
      (Fintype.card K - 1) * Nat.card (dimensionFiberContainingOne (K := K) k) := by
  rw [markedDimensionContainingOnePairs, Nat.card_prod, nonzeroValues_card]

theorem dimension_incidence_count (k : ℕ) :
    Nat.card (dimensionFiber (K := K) k) * (2 ^ k - 1) =
      (Fintype.card K - 1) * Nat.card (dimensionFiberContainingOne (K := K) k) := by
  calc
    _ = Nat.card (markedDimensionPairs (K := K) k) :=
      (markedDimensionPairs_card (K := K) k).symm
    _ = Nat.card (markedDimensionContainingOnePairs (K := K) k) :=
      Nat.card_congr (markedDimensionPairsEquivContainingOne (K := K) k)
    _ = _ := markedDimensionContainingOnePairs_card (K := K) k

set_option linter.style.haveILetI false in
theorem nonzeroCoefficient_count_identity (k : ℕ) (hk : 0 < k) (b : K) (hb : b ≠ 0) :
    (2 ^ k - 1) * Nat.card (coefficientFiber (K := K) k b) +
        Nat.card (zeroCoefficientFiberContainingOne (K := K) k) =
      Nat.card (dimensionFiberContainingOne (K := K) k) := by
  let q := Fintype.card K - 1
  let s := 2 ^ k - 1
  let G := Nat.card (dimensionFiber (K := K) k)
  let M0 := Nat.card (zeroCoefficientFiber (K := K) k)
  let Mb := Nat.card (coefficientFiber (K := K) k b)
  let h0 := Nat.card (zeroCoefficientFiberContainingOne (K := K) k)
  let B := Nat.card (dimensionFiberContainingOne (K := K) k)
  have htotal : G = M0 + q * Mb := by
    simpa [G, M0, Mb, q] using dimensionFiber_card_decomposition k hk b hb
  have hdim : G * s = q * B := by
    simpa [G, B, q, s] using dimension_incidence_count (K := K) k
  have hzero : M0 * s = q * h0 := by
    simpa [M0, h0, q, s] using zeroCoefficient_incidence_count (K := K) k hk
  have hq : 0 < q := by
    dsimp [q]
    haveI : Nonempty {v : K // v ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
    rw [← nonzeroValues_card]
    exact Nat.card_pos
  have hmul : q * B = q * (s * Mb + h0) := by
    calc
      q * B = G * s := hdim.symm
      _ = (M0 + q * Mb) * s := by rw [htotal]
      _ = M0 * s + q * (s * Mb) := by ring
      _ = q * h0 + q * (s * Mb) := by rw [hzero]
      _ = q * (s * Mb + h0) := by ring
  have := Nat.eq_of_mul_eq_mul_left hq hmul
  simpa [s, Mb, h0, B] using this.symm

#print axioms markedZeroSubspaceEquivOne
#print axioms markedZeroSubspacePairs_card_eq
#print axioms zeroCoefficient_incidence_count
#print axioms coefficientFibers_sum_card
#print axioms dimensionFiber_card_decomposition
#print axioms dimension_incidence_count
#print axioms nonzeroCoefficient_count_identity

end Carlet
