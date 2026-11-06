import Carlet.TransferOperator
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Linarith

noncomputable section

namespace Carlet.Transfer

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

attribute [local instance] Classical.propDecidable

def nonzeroCharacterTransform (ψ : AddChar K ℝ) (f : K → ℝ) (x : K) : ℝ :=
  ∑ v ∈ nonzeroElements, ψ (x / v) * f v

theorem nonzeroCharacterTransform_sum (ψ : AddChar K ℝ) (hψ : ψ ≠ 0)
    (f : K → ℝ) (hzero : (∑ x : K, f x) = 0) :
    (∑ x ∈ nonzeroElements, nonzeroCharacterTransform ψ f x) = f 0 := by
  classical
  calc
    _ = ∑ v ∈ nonzeroElements, f v *
        (∑ x ∈ nonzeroElements, ψ (x / v)) := by
      unfold nonzeroCharacterTransform
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_mul]
      ring
    _ = ∑ v ∈ nonzeroElements, f v * (-1) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [sum_nonzero_char_div ψ hψ v (Finset.mem_erase.mp hv).1]
    _ = -∑ v ∈ nonzeroElements, f v := by
      rw [← Finset.sum_mul]
      ring
    _ = f 0 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset K) f
        (Finset.mem_univ 0)
      have h' : (∑ v ∈ nonzeroElements, f v) + f 0 = 0 := by
        calc
          (∑ v ∈ nonzeroElements, f v) + f 0 = ∑ v : K, f v := by
            rw [nonzeroElements]
            exact h
          _ = 0 := hzero
      linarith

theorem sum_nonzero_char_mul (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (a : K) :
    (∑ x ∈ nonzeroElements, ψ (x * a)) =
      if a = 0 then (Fintype.card K : ℝ) - 1 else -1 := by
  classical
  by_cases ha : a = 0
  · rw [if_pos ha]
    subst a
    have hsum : (∑ x ∈ nonzeroElements, ψ (x * (0 : K))) =
        ((nonzeroElements (K := K)).card : ℝ) := by
      simp [nonzeroElements]
    have hcard : (nonzeroElements (K := K)).card + 1 = Fintype.card K := by
      exact Finset.card_erase_add_one (Finset.mem_univ 0)
    have hcardR : ((nonzeroElements (K := K)).card : ℝ) + 1 = Fintype.card K := by
      exact_mod_cast hcard
    rw [hsum, ← hcardR]
    ring
  · have hfull : (∑ x : K, ψ (x * a)) = 0 := by
      calc
        _ = ∑ x : K, ψ x := Fintype.sum_equiv (Equiv.mulRight₀ a ha)
          (fun x => ψ (x * a)) ψ (fun _ => rfl)
        _ = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
    have herase := Finset.sum_erase_add (Finset.univ : Finset K)
      (fun x => ψ (x * a)) (Finset.mem_univ 0)
    have hnonzero : (∑ x ∈ nonzeroElements, ψ (x * a)) + 1 = 0 := by
      simpa only [nonzeroElements, zero_mul, AddChar.map_zero_eq_one, hfull] using herase
    simp only [if_neg ha]
    linarith

theorem sum_nonzero_char_div_pair (ψ : AddChar K ℝ) (hψ : ψ ≠ 0)
    [CharP K 2] (v w : K) (_hv : v ≠ 0) (_hw : w ≠ 0) :
    (∑ x ∈ nonzeroElements, ψ (x / v) * ψ (x / w)) =
      if v = w then (Fintype.card K : ℝ) - 1 else -1 := by
  classical
  have hkernel : (∑ x ∈ nonzeroElements, ψ (x / v) * ψ (x / w)) =
      if v⁻¹ + w⁻¹ = 0 then (Fintype.card K : ℝ) - 1 else -1 := by
    calc
      _ = ∑ x ∈ nonzeroElements, ψ (x * (v⁻¹ + w⁻¹)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← AddChar.map_add_eq_mul]
        congr 1
        simp [div_eq_mul_inv, mul_add]
      _ = if v⁻¹ + w⁻¹ = 0 then (Fintype.card K : ℝ) - 1 else -1 :=
        sum_nonzero_char_mul ψ hψ (v⁻¹ + w⁻¹)
  have hinv : v⁻¹ + w⁻¹ = 0 ↔ v = w := by
    constructor
    · intro h
      have hinvEq : v⁻¹ = w⁻¹ := by
        simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp h)
      have h' := congrArg (fun z : K => z⁻¹) hinvEq
      simpa using h'
    · rintro rfl
      simp [CharTwo.add_self_eq_zero]
  by_cases hvw : v = w
  · have hzero : v⁻¹ + w⁻¹ = 0 := hinv.mpr hvw
    rw [hkernel, if_pos hzero, if_pos hvw]
  · have hne : v⁻¹ + w⁻¹ ≠ 0 := fun h => hvw (hinv.mp h)
    rw [hkernel, if_neg hne, if_neg hvw]

/-- Parseval's second-moment identity for the nonzero-character transform
in characteristic two. -/
theorem nonzeroCharacterTransform_sq_sum (ψ : AddChar K ℝ) (hψ : ψ ≠ 0)
    [CharP K 2] (f : K → ℝ) :
    (∑ x ∈ nonzeroElements, (nonzeroCharacterTransform ψ f x) ^ 2) =
      (Fintype.card K : ℝ) * (∑ v ∈ nonzeroElements, f v ^ 2) -
        (∑ v ∈ nonzeroElements, f v) ^ 2 := by
  classical
  have hdiag (v : K) (hv : v ∈ nonzeroElements) :
      (∑ w ∈ nonzeroElements, if v = w then
        (Fintype.card K : ℝ) * f v * f w else 0) =
        (Fintype.card K : ℝ) * f v ^ 2 := by
    have hdiag' :
        (∑ w ∈ nonzeroElements, if w = v then
          (Fintype.card K : ℝ) * f v * f w else 0) =
          (Fintype.card K : ℝ) * f v ^ 2 := by
      rw [Finset.sum_ite_eq' nonzeroElements v
        (fun w => (Fintype.card K : ℝ) * f v * f w)]
      simp [hv, pow_two]
      ring
    simpa only [eq_comm] using hdiag'
  have hsplit (v w : K) :
      f v * f w * (if v = w then (Fintype.card K : ℝ) - 1 else -1) =
        (if v = w then (Fintype.card K : ℝ) * f v * f w else 0) -
          f v * f w := by
    split_ifs <;> ring
  calc
    _ = ∑ x ∈ nonzeroElements, ∑ v ∈ nonzeroElements, ∑ w ∈ nonzeroElements,
          (ψ (x / v) * f v) * (ψ (x / w) * f w) := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold nonzeroCharacterTransform
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ v ∈ nonzeroElements, ∑ w ∈ nonzeroElements, ∑ x ∈ nonzeroElements,
          (ψ (x / v) * f v) * (ψ (x / w) * f w) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
    _ = ∑ v ∈ nonzeroElements, ∑ w ∈ nonzeroElements,
          f v * f w * (∑ x ∈ nonzeroElements, ψ (x / v) * ψ (x / w)) := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ v ∈ nonzeroElements, ∑ w ∈ nonzeroElements,
          f v * f w * (if v = w then (Fintype.card K : ℝ) - 1 else -1) := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [sum_nonzero_char_div_pair ψ hψ v w
        (Finset.mem_erase.mp hv).1 (Finset.mem_erase.mp hw).1]
    _ = (Fintype.card K : ℝ) * (∑ v ∈ nonzeroElements, f v ^ 2) -
          (∑ v ∈ nonzeroElements, f v) ^ 2 := by
      simp_rw [hsplit, Finset.sum_sub_distrib]
      have hfirst :
          (∑ v ∈ nonzeroElements, ∑ w ∈ nonzeroElements,
            if v = w then (Fintype.card K : ℝ) * f v * f w else 0) =
          (Fintype.card K : ℝ) * (∑ v ∈ nonzeroElements, f v ^ 2) := by
        calc
          _ = ∑ v ∈ nonzeroElements, (Fintype.card K : ℝ) * f v ^ 2 := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hdiag v hv
          _ = _ := by rw [Finset.mul_sum]
      have hsecond :
          (∑ v ∈ nonzeroElements, ∑ w ∈ nonzeroElements, f v * f w) =
            (∑ v ∈ nonzeroElements, f v) ^ 2 := by
        rw [← Finset.sum_mul_sum, pow_two]
      rw [hfirst, hsecond]

theorem nonzeroCharacterTransform_sq_sum_of_total_zero
    (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) [CharP K 2] (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) :
    (∑ x ∈ nonzeroElements, (nonzeroCharacterTransform ψ f x) ^ 2) =
      (Fintype.card K : ℝ) * ((∑ x : K, f x ^ 2) - (f 0) ^ 2) - (f 0) ^ 2 := by
  rw [nonzeroCharacterTransform_sq_sum ψ hψ]
  have hsumErase := Finset.sum_erase_add (Finset.univ : Finset K) f
    (Finset.mem_univ 0)
  have hnonzero : (∑ x ∈ nonzeroElements, f x) + f 0 = 0 := by
    calc
      (∑ x ∈ nonzeroElements, f x) + f 0 = ∑ x : K, f x := by
        rw [nonzeroElements]
        exact hsumErase
      _ = 0 := hzero
  have hsqErase := Finset.sum_erase_add (Finset.univ : Finset K)
    (fun x => f x ^ 2) (Finset.mem_univ 0)
  have hsq : (∑ x ∈ nonzeroElements, f x ^ 2) + f 0 ^ 2 =
      ∑ x : K, f x ^ 2 := by
    rw [nonzeroElements]
    exact hsqErase
  have hnonzero' : (∑ x ∈ nonzeroElements, f x) = -f 0 := by linarith
  have hsq' : (∑ x ∈ nonzeroElements, f x ^ 2) =
      (∑ x : K, f x ^ 2) - f 0 ^ 2 := by linarith
  rw [hnonzero', hsq']
  ring

/-- Exact one-step energy identity for the concrete transfer operator on
zero-sum functions. This is the coordinate form of Lemma 4.1. -/
theorem coreTransfer_sq_sum_of_total_zero
    (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) [CharP K 2] (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) :
    (∑ x : K, (coreTransfer ψ s f x) ^ 2) =
      ((Fintype.card K : ℝ) * (s - 1) ^ 2 / ((Fintype.card K : ℝ) - s) ^ 2) *
          (∑ x : K, f x ^ 2) +
        ((Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - s ^ 2) /
          ((Fintype.card K : ℝ) - s) ^ 2) * (f 0) ^ 2 := by
  classical
  let q : ℝ := Fintype.card K
  have hqcast : (nonzeroElements (K := K)).card + 1 = Fintype.card K :=
    Finset.card_erase_add_one (Finset.mem_univ 0)
  have hq : ((nonzeroElements (K := K)).card : ℝ) + 1 = q := by
    dsimp [q]
    exact_mod_cast hqcast
  have hsumErase := Finset.sum_erase_add (Finset.univ : Finset K) f
    (Finset.mem_univ 0)
  have hsumNZ : (∑ v ∈ nonzeroElements, f v) = -f 0 := by
    have hsplit : (∑ v ∈ nonzeroElements, f v) + f 0 = 0 := by
      calc
        _ = ∑ v : K, f v := by rw [nonzeroElements]; exact hsumErase
        _ = 0 := hzero
    linarith
  have hFsum := nonzeroCharacterTransform_sum ψ hψ f hzero
  have hFsq := nonzeroCharacterTransform_sq_sum_of_total_zero ψ hψ f hzero
  have hnum (x : K) (hx : x ∈ nonzeroElements) :
      transferNumerator ψ s f x =
        -f 0 + (s - 1) * nonzeroCharacterTransform ψ f x := by
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    unfold transferNumerator
    rw [if_neg hx0]
    calc
      (∑ v ∈ nonzeroElements, (1 + (s - 1) * ψ (x / v)) * f v) =
          (∑ v ∈ nonzeroElements, f v) +
            (s - 1) * (∑ v ∈ nonzeroElements, ψ (x / v) * f v) := by
        calc
          _ = ∑ v ∈ nonzeroElements,
              (f v + (s - 1) * (ψ (x / v) * f v)) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = -f 0 + (s - 1) * nonzeroCharacterTransform ψ f x := by
        rw [hsumNZ]
        rfl
  have hcore0 : coreTransfer ψ s f 0 = f 0 := by
    unfold coreTransfer transferNumerator
    simp
    field_simp [hs]
  have hnonzeroSq : (∑ x ∈ nonzeroElements, (coreTransfer ψ s f x) ^ 2) =
      ((Fintype.card K : ℝ) - s)⁻¹ ^ 2 *
        (∑ x ∈ nonzeroElements,
          (-f 0 + (s - 1) * nonzeroCharacterTransform ψ f x) ^ 2) := by
    calc
      _ = ∑ x ∈ nonzeroElements,
          ((-f 0 + (s - 1) * nonzeroCharacterTransform ψ f x) /
            ((Fintype.card K : ℝ) - s)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [coreTransfer, hnum x hx]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [div_pow]
        field_simp [hs]
  have hquad :
      (∑ x ∈ nonzeroElements,
        (-f 0 + (s - 1) * nonzeroCharacterTransform ψ f x) ^ 2) =
        ((nonzeroElements (K := K)).card : ℝ) * (f 0) ^ 2 -
          2 * f 0 * (s - 1) * f 0 + (s - 1) ^ 2 *
            (∑ x ∈ nonzeroElements, (nonzeroCharacterTransform ψ f x) ^ 2) := by
    calc
      _ = ∑ x ∈ nonzeroElements,
          ((f 0) ^ 2 - 2 * f 0 * (s - 1) * nonzeroCharacterTransform ψ f x +
            (s - 1) ^ 2 * (nonzeroCharacterTransform ψ f x) ^ 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]
        simp [Finset.sum_const, hFsum]
  have hsplit : (∑ x : K, (coreTransfer ψ s f x) ^ 2) =
      (f 0) ^ 2 + (∑ x ∈ nonzeroElements, (coreTransfer ψ s f x) ^ 2) := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset K)
      (fun x => (coreTransfer ψ s f x) ^ 2) (Finset.mem_univ 0)]
    simp [nonzeroElements, add_comm, hcore0]
  rw [hsplit, hnonzeroSq, hquad, hFsq]
  dsimp [q] at hq hs
  have hcardNZ : ((nonzeroElements (K := K)).card : ℝ) =
      (Fintype.card K : ℝ) - 1 := by linarith [hq]
  rw [hcardNZ]
  field_simp [hs]
  ring

theorem transfer_sq_sum_of_total_zero
    (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) [CharP K 2] (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) :
    (∑ b : K, (transfer ψ s f b) ^ 2) =
      ((Fintype.card K : ℝ) * (s - 1) ^ 2 / ((Fintype.card K : ℝ) - s) ^ 2) *
          (∑ x : K, f x ^ 2) +
        ((Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - s ^ 2) /
          ((Fintype.card K : ℝ) - s) ^ 2) * (f 0) ^ 2 := by
  calc
    _ = ∑ x : K, (coreTransfer ψ s f x) ^ 2 := by
      simpa only [transfer, sub_eq_add_neg] using
        (Fintype.sum_equiv (Equiv.addRight (-1 : K))
          (fun x => (coreTransfer ψ s f (x + (-1))) ^ 2)
          (fun x => (coreTransfer ψ s f x) ^ 2) (fun _ => rfl))
    _ = _ := coreTransfer_sq_sum_of_total_zero ψ hψ s hs f hzero

#print axioms sum_nonzero_char_mul
#print axioms sum_nonzero_char_div_pair
#print axioms nonzeroCharacterTransform_sq_sum
#print axioms nonzeroCharacterTransform_sq_sum_of_total_zero
#print axioms coreTransfer_sq_sum_of_total_zero
#print axioms transfer_sq_sum_of_total_zero
#print axioms nonzeroCharacterTransform_sum

/-!
The final scalar estimate in the two-step contraction argument.  Here `t`
stands for `sqrt q`, and the first summand is `alpha_(2s)`; the hypothesis
`q ≥ 32 s^2` is the range used in the paper's Lemma 4.2.
-/
theorem twoStep_scalar_bound (q s t : ℝ)
    (hs : 2 ≤ s) (ht : 0 < t) (htq : t ^ 2 = q)
    (hq : 32 * s ^ 2 ≤ q) :
    t * (2 * s - 1) / (q - 2 * s) + 1 / (q - 1) < 2 * s / t := by
  have hspos : 0 < s := by linarith
  have hqpos : 0 < q := by nlinarith [htq]
  have hqge128 : 128 ≤ q := by nlinarith [hq]
  have hqminus2 : 0 < q - 2 * s := by nlinarith [hq]
  have hqminus1 : 0 < q - 1 := by linarith
  have hqminus4 : 0 < q - 4 * s ^ 2 := by nlinarith [hq]
  have hgap : 2 * s / t - t * (2 * s - 1) / (q - 2 * s) =
      (q - 4 * s ^ 2) / (t * (q - 2 * s)) := by
    field_simp [ht.ne', hqminus2.ne']
    rw [← htq]
    ring
  have hprodLower : (7 / 16 : ℝ) * q ^ 2 ≤
      (q - 1) * (q - 4 * s ^ 2) := by
    have hleft : q / 2 ≤ q - 1 := by linarith
    have hright : (7 / 8 : ℝ) * q ≤ q - 4 * s ^ 2 := by nlinarith [hq]
    have hmul₁ := mul_le_mul_of_nonneg_right hleft hqminus4.le
    have hmul₂ := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ q / 2)
    nlinarith [hmul₁, hmul₂]
  have htge8 : 8 ≤ t := by
    by_contra h
    have hprod : 0 ≤ (8 - t) * (8 + t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [htq, hqge128, hprod]
  have htleq : t ≤ q / 8 := by
    have hprod : 0 ≤ (t - 8) * t := mul_nonneg (by linarith) ht.le
    nlinarith [htq, hprod]
  have hsmall : t * (q - 2 * s) < q ^ 2 / 8 := by
    have hstrict : t * (q - 2 * s) < t * q := by
      exact mul_lt_mul_of_pos_left (by linarith) ht
    have hweak : t * q ≤ q ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_right htleq hqpos.le
      nlinarith [htq, this]
    linarith
  have hnum : t * (q - 2 * s) < (q - 1) * (q - 4 * s ^ 2) := by
    have hq2pos : 0 < q ^ 2 := by positivity
    nlinarith [hprodLower, hsmall, hq2pos]
  have hfrac : 1 / (q - 1) < (q - 4 * s ^ 2) / (t * (q - 2 * s)) :=
    (div_lt_div_iff₀ hqminus1 (mul_pos ht hqminus2)).2 (by
      simpa [mul_comm] using hnum)
  linarith [hgap, hfrac]

theorem oneStep_scalar_nonexpansive (q s t : ℝ)
    (hs : 1 ≤ s) (hsq : s ^ 2 ≤ q) (hsqStrict : s < q)
    (ht : 0 < t) (htq : t ^ 2 = q) :
    t * (s - 1) / (q - s) ≤ 1 := by
  have hqpos : 0 < q := by nlinarith [htq]
  have hqminus1 : 0 ≤ q - 1 := by nlinarith [hsq, hs]
  have hden : 0 < q - s := by linarith
  have hnum : 0 ≤ t * (s - 1) := by positivity
  have hidentity : (q - s) ^ 2 - (t * (s - 1)) ^ 2 =
      (q - 1) * (q - s ^ 2) := by
    rw [← htq]
    ring
  have hsquares : (t * (s - 1)) ^ 2 ≤ (q - s) ^ 2 := by
    have hright : 0 ≤ (q - 1) * (q - s ^ 2) :=
      mul_nonneg hqminus1 (by nlinarith [hsq])
    nlinarith [hidentity]
  have hlinear : t * (s - 1) ≤ q - s := by
    by_contra h
    have hgt : q - s < t * (s - 1) := lt_of_not_ge h
    have hsum : 0 < q - s + t * (s - 1) := by linarith
    have hprod : 0 < (t * (s - 1) - (q - s)) *
        (t * (s - 1) + (q - s)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hsquares, hprod]
  exact (div_le_iff₀ hden).2 (by simpa using hlinear)

#print axioms twoStep_scalar_bound
#print axioms oneStep_scalar_nonexpansive

end Carlet.Transfer
