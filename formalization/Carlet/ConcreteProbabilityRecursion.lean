import Carlet.AdjacentCountRatio
import Carlet.ArtinSchreierPolynomial

noncomputable section

open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance probabilityNonzeroFintype : Fintype {v : K // v ≠ 0} := Fintype.ofFinite _

local instance probabilitySubmoduleFinite : Finite (Submodule (ZMod 2) K) :=
  Finite.of_injective (fun E : Submodule (ZMod 2) K => (E : Set K)) SetLike.coe_injective

local instance probabilityContainingFiberFinite (d : ℕ) (b : K) :
    Finite (containingOneCoefficientFiber (K := K) d b) :=
  Finite.of_injective (fun H : containingOneCoefficientFiber (K := K) d b => H.val)
    Subtype.val_injective

local instance probabilityContainingFiberFintype (d : ℕ) (b : K) :
    Fintype (containingOneCoefficientFiber (K := K) d b) := Fintype.ofFinite _

local instance probabilityContainingOneFinite (d : ℕ) :
    Finite (dimensionFiberContainingOne (K := K) d) :=
  Finite.of_injective (fun H : dimensionFiberContainingOne (K := K) d => H.val)
    Subtype.val_injective

local instance probabilityContainingOneFintype (d : ℕ) :
    Fintype (dimensionFiberContainingOne (K := K) d) := Fintype.ofFinite _

def containingOneCoefficientFibersEquiv (d : ℕ) :
    (Σ b : K, containingOneCoefficientFiber (K := K) d b) ≃
      dimensionFiberContainingOne (K := K) d where
  toFun p := ⟨p.2.val, p.2.property.1, p.2.property.2.1⟩
  invFun H := ⟨nextFrobeniusCoefficient H.val, ⟨H.val, H.property.1,
    H.property.2, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨b, ⟨H, hdim, hone, hcoeff⟩⟩
    apply Sigma.ext hcoeff
    cases hcoeff
    rfl
  right_inv H := by
    apply Subtype.ext
    rfl

def containingOneCoefficientProbability (d : ℕ) (b : K) : ℝ :=
  (Nat.card (containingOneCoefficientFiber (K := K) d b) : ℝ) /
    (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ)

omit [DecidableEq K] in
theorem dimensionOneContainingOne_eq_primeLine
    (H : dimensionFiberContainingOne (K := K) 1) :
    H.val = Submodule.span (ZMod 2) ({1} : Set K) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr H.property.2
  · rw [finrank_span_singleton (K := ZMod 2) (V := K)
      (v := (1 : K)) one_ne_zero, H.property.1]

theorem nextFrobeniusCoefficient_dimensionOneContainingOne
    (H : dimensionFiberContainingOne (K := K) 1) :
    nextFrobeniusCoefficient H.val = 1 := by
  rw [dimensionOneContainingOne_eq_primeLine H]
  unfold nextFrobeniusCoefficient
  rw [finrank_span_singleton (K := ZMod 2) (V := K)
    (v := (1 : K)) one_ne_zero, primeLine_polynomial]
  norm_num

theorem containingOne_probability_one_dim (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hnpos : 1 ≤ n) (b : K) :
    containingOneCoefficientProbability (K := K) 1 b = if b = 1 then 1 else 0 := by
  classical
  by_cases hb : b = 1
  · subst b
    let e : containingOneCoefficientFiber (K := K) 1 1 ≃
        dimensionFiberContainingOne (K := K) 1 := {
      toFun H := ⟨H.val, H.property.1, H.property.2.1⟩
      invFun H := ⟨H.val, H.property.1, H.property.2,
        nextFrobeniusCoefficient_dimensionOneContainingOne (K := K) H⟩
      left_inv H := by
        apply Subtype.ext
        rfl
      right_inv H := by
        apply Subtype.ext
        rfl
    }
    have hD : (Nat.card (dimensionFiberContainingOne (K := K) 1) : ℝ) ≠ 0 := by
      have hp := dimensionFiberContainingOne_card_pos n 1 hn (by omega) hnpos
      exact_mod_cast (Nat.ne_of_gt hp)
    rw [if_pos rfl]
    change (Nat.card (containingOneCoefficientFiber (K := K) 1 1) : ℝ) /
      (Nat.card (dimensionFiberContainingOne (K := K) 1) : ℝ) = 1
    rw [Nat.card_congr e]
    exact div_self hD
  · have hempty : IsEmpty (containingOneCoefficientFiber (K := K) 1 b) := by
      refine ⟨fun H => ?_⟩
      rcases H with ⟨E, hdim, hone, hcoeff⟩
      let D : dimensionFiberContainingOne (K := K) 1 := ⟨E, hdim, hone⟩
      have hpoint := nextFrobeniusCoefficient_dimensionOneContainingOne (K := K) D
      change nextFrobeniusCoefficient E = 1 at hpoint
      exact hb (hcoeff.symm.trans hpoint)
    rw [if_neg hb]
    change (Nat.card (containingOneCoefficientFiber (K := K) 1 b) : ℝ) /
      (Nat.card (dimensionFiberContainingOne (K := K) 1) : ℝ) = 0
    have hcard : Nat.card (containingOneCoefficientFiber (K := K) 1 b) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero_iff.mpr hempty
    rw [hcard]
    simp

#print axioms dimensionOneContainingOne_eq_primeLine
#print axioms nextFrobeniusCoefficient_dimensionOneContainingOne
#print axioms containingOne_probability_one_dim

omit [DecidableEq K] in
theorem containingOne_probability_sum (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 0 < d) (hdn : d ≤ n) :
    (∑ b : K, containingOneCoefficientProbability (K := K) d b) = 1 := by
  classical
  let D := (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast dimensionFiberContainingOne_card_pos n d hn hd hdn
  have hD : D ≠ 0 := ne_of_gt hDpos
  have hsumCard :
      (∑ b : K, Nat.card (containingOneCoefficientFiber (K := K) d b)) =
        Nat.card (dimensionFiberContainingOne (K := K) d) := by
    calc
      _ = Nat.card (Σ b : K, containingOneCoefficientFiber (K := K) d b) :=
        Nat.card_sigma.symm
      _ = Nat.card (dimensionFiberContainingOne (K := K) d) :=
        Nat.card_congr (containingOneCoefficientFibersEquiv (K := K) d)
  simp only [containingOneCoefficientProbability]
  change (∑ b : K,
    (Nat.card (containingOneCoefficientFiber (K := K) d b) : ℝ) / D) = 1
  rw [← Finset.sum_div, ← Nat.cast_sum, hsumCard]
  change D / D = 1
  exact div_self hD

#print axioms containingOne_probability_sum

theorem containingOne_probability_nonzero_sum (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 0 < d) (hdn : d ≤ n) :
    (∑ v : {v : K // v ≠ 0}, containingOneCoefficientProbability (K := K) d v.val) =
      1 - containingOneCoefficientProbability (K := K) d 0 := by
  classical
  have htotal := containingOne_probability_sum (K := K) n d hn hd hdn
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset K)
    (containingOneCoefficientProbability (K := K) d) (Finset.mem_univ 0)
  have hsubtype :
      (∑ v : {v : K // v ≠ 0}, containingOneCoefficientProbability (K := K) d v.val) =
        ∑ v ∈ (Finset.univ : Finset K).erase 0,
          containingOneCoefficientProbability (K := K) d v := by
    symm
    exact Finset.sum_subtype ((Finset.univ : Finset K).erase 0)
      (by intro v; simp [Finset.mem_erase])
      (fun v => containingOneCoefficientProbability (K := K) d v)
  rw [hsubtype]
  have hfull :
      (∑ v ∈ (Finset.univ : Finset K).erase 0,
        containingOneCoefficientProbability (K := K) d v) +
          containingOneCoefficientProbability (K := K) d 0 = 1 := by
    have htotalFin :
        (∑ v ∈ (Finset.univ : Finset K),
          containingOneCoefficientProbability (K := K) d v) = 1 := by
      simpa using htotal
    rw [htotalFin] at hsplit
    exact hsplit
  linarith

#print axioms containingOne_probability_nonzero_sum

def normalizedReciprocalFiberSum (d : ℕ) (b : K) : ℝ :=
  ∑ w : {w : K // w ≠ 0},
    traceCharacter (K := K) w.val *
      containingOneCoefficientProbability (K := K) d (b / w.val)

def nonzeroDivisionEquiv (x : K) (hx : x ≠ 0) :
    {v : K // v ≠ 0} ≃ {v : K // v ≠ 0} where
  toFun v := ⟨x / v.val, div_ne_zero hx v.property⟩
  invFun v := ⟨x / v.val, div_ne_zero hx v.property⟩
  left_inv v := by
    apply Subtype.ext
    field_simp [hx, v.property]
  right_inv v := by
    apply Subtype.ext
    field_simp [hx, v.property]

omit [Algebra (ZMod 2) K] [DecidableEq K] in
theorem trace_weighted_reciprocal_reindex (ψ : AddChar K ℝ) (x : K) (hx : x ≠ 0)
    (f : K → ℝ) :
    (∑ w : {w : K // w ≠ 0}, ψ w.val * f (x / w.val)) =
      ∑ v : {v : K // v ≠ 0}, ψ (x / v.val) * f v.val := by
  classical
  exact Fintype.sum_equiv (nonzeroDivisionEquiv x hx)
    (fun w => ψ w.val * f (x / w.val))
    (fun v => ψ (x / v.val) * f v.val) (by
      intro v
      have hv : x / (x / v.val) = v.val := by
        field_simp [hx, v.property]
      simp [nonzeroDivisionEquiv, hv])

#print axioms trace_weighted_reciprocal_reindex

omit [DecidableEq K] in
theorem normalizedReciprocalFiberSum_eq_transform (d : ℕ) (x : K) (hx : x ≠ 0) :
    normalizedReciprocalFiberSum (K := K) d x =
      ∑ v : {v : K // v ≠ 0},
        traceCharacter (K := K) (x / v.val) *
          containingOneCoefficientProbability (K := K) d v.val := by
  unfold normalizedReciprocalFiberSum
  exact trace_weighted_reciprocal_reindex (traceCharacter (K := K)) x hx
    (fun y => containingOneCoefficientProbability (K := K) d y)

theorem containingOne_probability_nonzero_finset_sum (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 0 < d) (hdn : d ≤ n) :
    (∑ v ∈ Transfer.nonzeroElements (K := K),
      containingOneCoefficientProbability (K := K) d v) =
      1 - containingOneCoefficientProbability (K := K) d 0 := by
  classical
  have hsubtype := containingOne_probability_nonzero_sum (K := K) n d hn hd hdn
  calc
    _ = ∑ v : {v : K // v ≠ 0},
        containingOneCoefficientProbability (K := K) d v.val := by
      exact Finset.sum_subtype (Transfer.nonzeroElements (K := K))
        (by intro v; simp [Transfer.nonzeroElements])
        (fun v => containingOneCoefficientProbability (K := K) d v)
    _ = _ := hsubtype

omit [DecidableEq K] in
theorem normalizedReciprocalFiberSum_finset (d : ℕ) (x : K) (hx : x ≠ 0) :
    normalizedReciprocalFiberSum (K := K) d x =
      ∑ v ∈ Transfer.nonzeroElements (K := K),
        traceCharacter (K := K) (x / v) *
          containingOneCoefficientProbability (K := K) d v := by
  classical
  rw [normalizedReciprocalFiberSum_eq_transform (K := K) d x hx]
  symm
  exact Finset.sum_subtype (Transfer.nonzeroElements (K := K))
    (by intro v; simp [Transfer.nonzeroElements])
    (fun v => traceCharacter (K := K) (x / v) *
      containingOneCoefficientProbability (K := K) d v)

theorem transferNumerator_probability_nonzero (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 0 < d) (hdn : d ≤ n)
    (x : K) (hx : x ≠ 0) :
    Transfer.transferNumerator (traceCharacter (K := K)) (2 ^ d : ℝ)
        (containingOneCoefficientProbability (K := K) d) x =
      1 - containingOneCoefficientProbability (K := K) d 0 +
        ((2 ^ d : ℝ) - 1) * normalizedReciprocalFiberSum (K := K) d x := by
  classical
  rw [Transfer.transferNumerator, if_neg hx]
  calc
    (∑ v ∈ Transfer.nonzeroElements (K := K),
      (1 + ((2 ^ d : ℝ) - 1) * traceCharacter (K := K) (x / v)) *
        containingOneCoefficientProbability (K := K) d v) =
      (∑ v ∈ Transfer.nonzeroElements (K := K),
        containingOneCoefficientProbability (K := K) d v) +
        ((2 ^ d : ℝ) - 1) *
          (∑ v ∈ Transfer.nonzeroElements (K := K),
            traceCharacter (K := K) (x / v) *
              containingOneCoefficientProbability (K := K) d v) := by
      calc
        _ = ∑ v ∈ Transfer.nonzeroElements (K := K),
            (containingOneCoefficientProbability (K := K) d v +
              ((2 ^ d : ℝ) - 1) *
                (traceCharacter (K := K) (x / v) *
                  containingOneCoefficientProbability (K := K) d v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 1 - containingOneCoefficientProbability (K := K) d 0 +
        ((2 ^ d : ℝ) - 1) * normalizedReciprocalFiberSum (K := K) d x := by
      rw [containingOne_probability_nonzero_finset_sum (K := K) n d hn hd hdn,
        normalizedReciprocalFiberSum_finset (K := K) d x hx]

#print axioms transferNumerator_probability_nonzero

theorem containingOne_probability_recursion (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d < n) (b : K) (hb : b + 1 ≠ 0) :
    ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) *
        containingOneCoefficientProbability (K := K) (d + 1) b =
      1 - containingOneCoefficientProbability (K := K) d 0 +
        ((2 ^ d : ℝ) - 1) * normalizedReciprocalFiberSum (K := K) d (b + 1) := by
  let A := (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ)
  let B := (Nat.card (dimensionFiberContainingOne (K := K) (d + 1)) : ℝ)
  let Hnext := (Nat.card (containingOneCoefficientFiber (K := K) (d + 1) b) : ℝ)
  let Hzero := (Nat.card (containingOneCoefficientFiber (K := K) d 0) : ℝ)
  let M := (Nat.card (coefficientFiber (K := K) d (b + 1)) : ℝ)
  let C := ∑ w : {w : K // w ≠ 0},
    traceCharacter (K := K) w.val *
      (Nat.card (containingOneCoefficientFiber (K := K) d ((b + 1) / w.val)) : ℝ)
  let W := normalizedReciprocalFiberSum (K := K) d (b + 1)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact_mod_cast (Nat.ne_of_gt
      (dimensionFiberContainingOne_card_pos n d hn (by omega) (by omega)))
  have hB : B ≠ 0 := by
    dsimp [B]
    exact_mod_cast (Nat.ne_of_gt
      (dimensionFiberContainingOne_card_pos n (d + 1) hn (by omega) (by omega)))
  have hs : (2 ^ d : ℝ) - 1 ≠ 0 := by
    have hpow : (1 : ℝ) < (2 ^ d : ℝ) := by
      have hnat : 1 < 2 ^ d := Nat.one_lt_pow (Nat.ne_of_gt hd) (by decide)
      exact_mod_cast hnat
    linarith
  have htwo : (2 ^ d : ℝ) ≠ 0 := by positivity
  have hRatio : B / A =
      ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) /
        ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) := by
    dsimp [A, B]
    exact adjacentOneFiber_real_ratio_of_bounds n d hn hd (by omega)
  have hRawCount : (2 ^ d : ℝ) * Hnext = M + C := by
    simpa [Hnext, M, C, reciprocalFiberCharacterTerm] using
      artinSchreier_character_count_recursion_reindexed (K := K) d hd b
  have hIncNat := nonzeroCoefficient_count_identity (K := K) d hd (b + 1) hb
  have hsub : (↑(2 ^ d - 1 : ℕ) : ℝ) = (2 ^ d : ℝ) - 1 := by
    have hpowPos : 0 < 2 ^ d := by positivity
    have hpos : 1 ≤ 2 ^ d := Nat.succ_le_iff.mpr hpowPos
    rw [Nat.cast_sub hpos, Nat.cast_pow]
    norm_num
  have hInc : ((2 ^ d : ℝ) - 1) * M + Hzero = A := by
    dsimp [M, Hzero, A]
    have hcast := congrArg (fun z : ℕ => (z : ℝ)) hIncNat
    rw [Nat.cast_add, Nat.cast_mul, hsub] at hcast
    exact hcast
  have hW : W = C / A := by
    dsimp [W, C, normalizedReciprocalFiberSum, containingOneCoefficientProbability]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hRaw : (2 ^ d : ℝ) * B * (Hnext / B) =
      A * ((1 - Hzero / A) / ((2 ^ d : ℝ) - 1) + W) := by
    rw [hW]
    field_simp [hA, hB, hs, htwo]
    nlinarith [hInc, hRawCount]
  have hNorm := normalized_recursion_from_raw_counts
    ((2 ^ d : ℝ)) (Fintype.card K) A B (Hnext / B) (Hzero / A) W
    ((2 ^ d : ℝ)) hA hs htwo hRatio hRaw
  simpa [containingOneCoefficientProbability, normalizedReciprocalFiberSum,
    A, B, Hnext, Hzero, W] using hNorm

#print axioms containingOne_probability_recursion

theorem containingOne_probability_boundary (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d < n) :
    containingOneCoefficientProbability (K := K) (d + 1) 1 =
      containingOneCoefficientProbability (K := K) d 0 := by
  classical
  let A := (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ)
  let B := (Nat.card (dimensionFiberContainingOne (K := K) (d + 1)) : ℝ)
  let Hnext := (Nat.card (containingOneCoefficientFiber (K := K) (d + 1) 1) : ℝ)
  let Hzero := (Nat.card (containingOneCoefficientFiber (K := K) d 0) : ℝ)
  let Mzero := (Nat.card (coefficientFiber (K := K) d 0) : ℝ)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact_mod_cast (Nat.ne_of_gt
      (dimensionFiberContainingOne_card_pos n d hn (by omega) (by omega)))
  have hB : B ≠ 0 := by
    dsimp [B]
    exact_mod_cast (Nat.ne_of_gt
      (dimensionFiberContainingOne_card_pos n (d + 1) hn (by omega) (by omega)))
  have hs : (2 ^ d : ℝ) - 1 ≠ 0 := by
    have hpow : (1 : ℝ) < (2 ^ d : ℝ) := by
      have hnat : 1 < 2 ^ d := Nat.one_lt_pow (Nat.ne_of_gt hd) (by decide)
      exact_mod_cast hnat
    linarith
  have htwo : (2 ^ d : ℝ) ≠ 0 := by positivity
  have hRatio : B / A =
      ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) /
        ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) := by
    dsimp [A, B]
    exact adjacentOneFiber_real_ratio_of_bounds n d hn hd (by omega)
  have hsumFin : (∑ w ∈ Transfer.nonzeroElements (K := K),
      traceCharacter (K := K) w) = -1 := by
    simpa [Transfer.nonzeroElements, div_one] using
      (Transfer.sum_nonzero_char_div (traceCharacter (K := K))
        (traceCharacter_ne_zero (K := K)) (1 : K) one_ne_zero)
  have hsum : (∑ w : {w : K // w ≠ 0}, traceCharacter (K := K) w.val) = -1 := by
    calc
      _ = ∑ w ∈ (Finset.univ : Finset K).erase 0, traceCharacter (K := K) w := by
        symm
        exact Finset.sum_subtype ((Finset.univ : Finset K).erase 0)
          (by intro w; simp [Finset.mem_erase])
          (fun w => traceCharacter (K := K) w)
      _ = -1 := by simpa [Transfer.nonzeroElements] using hsumFin
  have hcharZero : (∑ w : {w : K // w ≠ 0},
      traceCharacter (K := K) w.val * Hzero) = -Hzero := by
    calc
      _ = (∑ w : {w : K // w ≠ 0}, traceCharacter (K := K) w.val) * Hzero :=
        (Finset.sum_mul _ _ _).symm
      _ = -Hzero := by rw [hsum]; ring
  have hraw : (2 ^ d : ℝ) * Hnext = Mzero - Hzero := by
    have hrec := artinSchreier_character_count_recursion_reindexed (K := K) d hd (1 : K)
    have hone : (1 : K) + 1 = 0 := by
      have htwoZ : (1 : ZMod 2) + 1 = 0 := by decide
      simpa using congrArg (algebraMap (ZMod 2) K) htwoZ
    rw [hone] at hrec
    have hterms : (∑ w : {w : K // w ≠ 0},
        reciprocalFiberCharacterTerm (K := K) d 0 w) = -Hzero := by
      simpa [reciprocalFiberCharacterTerm, Hzero, zero_div] using hcharZero
    rw [hterms] at hrec
    simpa [Hnext, Mzero, sub_eq_add_neg] using hrec
  have hIncNat := zeroCoefficient_incidence_count (K := K) d (by omega)
  have hsub : (↑(2 ^ d - 1 : ℕ) : ℝ) = (2 ^ d : ℝ) - 1 := by
    have hp : 0 < 2 ^ d := by positivity
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hp), Nat.cast_pow]
    norm_num
  have hInc : ((2 ^ d : ℝ) - 1) * Mzero =
      ((Fintype.card K : ℝ) - 1) * Hzero := by
    have hIncNat' : Nat.card (coefficientFiber (K := K) d 0) * (2 ^ d - 1) =
        (Fintype.card K - 1) *
          Nat.card (containingOneCoefficientFiber (K := K) d 0) := by
      simpa [zeroCoefficientFiber, zeroCoefficientFiberContainingOne,
        containingOneCoefficientFiber] using hIncNat
    have hcast := congrArg (fun z : ℕ => (z : ℝ)) hIncNat'
    have hcardK : 1 ≤ Fintype.card K := by
      have hpos : 0 < Fintype.card K := Fintype.card_pos
      omega
    have hqsub : (↑(Fintype.card K - 1 : ℕ) : ℝ) =
        (Fintype.card K : ℝ) - 1 := by
      rw [Nat.cast_sub hcardK]
      norm_num
    rw [Nat.cast_mul, hsub, Nat.cast_mul, hqsub] at hcast
    dsimp [Mzero, Hzero]
    nlinarith [hcast]
  have hcross : (2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1) * Hnext =
      ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) * Hzero := by
    nlinarith [hraw, hInc]
  change Hnext / B = Hzero / A
  field_simp [hA, hB]
  have hRatioCross := hRatio
  field_simp [hA, hs, htwo] at hRatioCross
  have hcross' :
      ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) * Hnext =
        ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) * Hzero := by
    nlinarith [hcross]
  have hratio' :
      ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) * B =
        ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) * A := by
    nlinarith [hRatioCross]
  have hc : (2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1) ≠ 0 := mul_ne_zero htwo hs
  have hcancel : Hnext * A = Hzero * B := by
    apply (mul_left_cancel₀ hc)
    calc
      ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) * (Hnext * A) =
          ((((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) * Hnext) * A) := by ring
      _ = ((((Fintype.card K : ℝ) - (2 ^ d : ℝ)) * Hzero) * A) := by rw [hcross']
      _ = ((((Fintype.card K : ℝ) - (2 ^ d : ℝ)) * A) * Hzero) := by ring
      _ = ((((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) * B) * Hzero) := by rw [hratio']
      _ = ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) * (Hzero * B) := by ring
  nlinarith [hcancel]

#print axioms containingOne_probability_boundary

set_option linter.style.haveILetI false in
theorem containingOne_probability_transfer (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d < n) (b : K) :
    Transfer.transfer (traceCharacter (K := K)) (2 ^ d : ℝ)
        (containingOneCoefficientProbability (K := K) d) b =
      containingOneCoefficientProbability (K := K) (d + 1) b := by
  classical
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hcardNat : Fintype.card K = 2 ^ n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    simpa only [ZMod.card, hn] using h
  have hpowlt : 2 ^ d < 2 ^ n := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hdn
  have hpowltR : (2 ^ d : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hpowlt
  have hden : (Fintype.card K : ℝ) - (2 ^ d : ℝ) ≠ 0 := by
    have hcast : (Fintype.card K : ℝ) = (2 ^ n : ℝ) := by exact_mod_cast hcardNat
    rw [hcast]
    linarith
  have hneg : (-1 : K) = 1 := by
    calc
      -1 = -((1 : K) + 1) + 1 := by ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero]; simp
  have hshift (x : K) : x - 1 = x + 1 := by
    rw [sub_eq_add_neg, hneg]
  by_cases hb : b + 1 = 0
  · have hb1 : b = 1 := by
      have heq : b + 1 = (1 : K) + 1 := by rw [hb, CharTwo.add_self_eq_zero]
      exact add_right_cancel heq
    have hzero : b - 1 = 0 := by rw [hb1]; simp
    rw [Transfer.transfer, Transfer.coreTransfer, hzero,
      Transfer.transferNumerator, if_pos rfl]
    simp only [mul_div_cancel_left₀ _ hden]
    rw [hb1, containingOne_probability_boundary n d hn hd hdn]
  · have hnonzero : b + 1 ≠ 0 := hb
    have hrec := containingOne_probability_recursion n d hn hd hdn b hnonzero
    have hnum := transferNumerator_probability_nonzero (K := K) n d hn hd
      (by omega) (b + 1) hnonzero
    rw [Transfer.transfer, Transfer.coreTransfer, hshift b, hnum]
    rw [← hrec]
    exact mul_div_cancel_left₀ _ hden

#print axioms containingOne_probability_transfer

end Carlet
