import Carlet.TransferContraction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

namespace Carlet.Transfer

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

attribute [local instance] Classical.propDecidable

def centeredDelta (a x : K) : ℝ :=
  (if x = a then 1 else 0) - 1 / (Fintype.card K : ℝ)

theorem transferNumerator_sub (ψ : AddChar K ℝ) (s : ℝ) (f g : K → ℝ) (x : K) :
    transferNumerator ψ s (fun v => f v - g v) x =
      transferNumerator ψ s f x - transferNumerator ψ s g x := by
  classical
  by_cases hx : x = 0
  · simp [transferNumerator, hx, mul_sub]
  · simp only [transferNumerator, if_neg hx, mul_sub, Finset.sum_sub_distrib]

theorem transfer_sub (ψ : AddChar K ℝ) (s : ℝ) (f g : K → ℝ) (b : K) :
    transfer ψ s (fun v => f v - g v) b =
      transfer ψ s f b - transfer ψ s g b := by
  simp only [transfer, coreTransfer, transferNumerator_sub, sub_div]

theorem transfer_smul (ψ : AddChar K ℝ) (s c : ℝ) (f : K → ℝ) (b : K) :
    transfer ψ s (fun v => c * f v) b = c * transfer ψ s f b := by
  simp only [transfer, coreTransfer, transferNumerator_smul, mul_div_assoc]

theorem coreTransfer_delta_zero (ψ : AddChar K ℝ) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (x : K) :
    coreTransfer ψ s (fun v => if v = 0 then 1 else 0) x =
      if x = 0 then 1 else 0 := by
  classical
  by_cases hx : x = 0
  · simp [coreTransfer, transferNumerator, hx, hs]
  · simp only [coreTransfer, transferNumerator, if_neg hx]
    have hsum : (∑ v ∈ nonzeroElements,
        (1 + (s - 1) * ψ (x / v)) * (if v = 0 then (1 : ℝ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp [(Finset.mem_erase.mp hv).1]
    rw [hsum, zero_div]

theorem transfer_delta_zero (ψ : AddChar K ℝ) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (b : K) :
    transfer ψ s (fun v => if v = 0 then 1 else 0) b =
      if b = 1 then 1 else 0 := by
  rw [transfer, coreTransfer_delta_zero ψ s hs]
  simp only [sub_eq_zero]

theorem transfer_centeredDelta_zero (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (b : K) :
    transfer ψ s (centeredDelta 0) b = centeredDelta 1 b := by
  change transfer ψ s (fun v => (if v = 0 then 1 else 0) -
    1 / (Fintype.card K : ℝ)) b = _
  rw [transfer_sub, transfer_delta_zero ψ s hs,
    transfer_constant ψ hψ s (1 / (Fintype.card K : ℝ)) hs]
  rfl

theorem centeredDelta_sum (a : K) : (∑ x : K, centeredDelta a x) = 0 := by
  classical
  have hq : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [centeredDelta, Finset.sum_sub_distrib, Finset.sum_ite_eq', hq]

theorem centeredDelta_sq_sum (a : K) :
    (∑ x : K, centeredDelta a x ^ 2) = 1 - 1 / (Fintype.card K : ℝ) := by
  classical
  have hq : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hpoint (x : K) : centeredDelta a x ^ 2 =
      (if x = a then (1 : ℝ) else 0) * (1 - 2 / (Fintype.card K : ℝ)) +
        (1 / (Fintype.card K : ℝ)) ^ 2 := by
    by_cases hx : x = a
    · simp [centeredDelta, hx]
      ring
    · simp [centeredDelta, hx]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  simp [Finset.sum_ite_eq']
  field_simp [hq]
  ring

omit [Field K] in
theorem sum_mul_centeredDelta_of_total_zero (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) (a : K) :
    (∑ x : K, f x * centeredDelta a x) = f a := by
  classical
  simp only [centeredDelta, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hzero, zero_mul, sub_zero]
  simp [mul_ite, Finset.sum_ite_eq']

theorem energy_sub_centeredDelta (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) (a : K) (c : ℝ) :
    (∑ x : K, (f x - c * centeredDelta a x) ^ 2) =
      (∑ x : K, f x ^ 2) - 2 * c * f a +
        c ^ 2 * (1 - 1 / (Fintype.card K : ℝ)) := by
  have hpoint (x : K) : (f x - c * centeredDelta a x) ^ 2 =
      f x ^ 2 - (2 * c) * (f x * centeredDelta a x) +
        c ^ 2 * centeredDelta a x ^ 2 := by ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_mul_centeredDelta_of_total_zero f hzero a, centeredDelta_sq_sum]

def energy (f : K → ℝ) : ℝ := ∑ x : K, f x ^ 2

def meanZeroWeight (K : Type*) [Fintype K] : ℝ := 1 - 1 / (Fintype.card K : ℝ)

def transferScaleSq (K : Type*) [Fintype K] (s : ℝ) : ℝ :=
  (Fintype.card K : ℝ) * (s - 1) ^ 2 / ((Fintype.card K : ℝ) - s) ^ 2

omit [Field K] in
theorem energy_nonneg (f : K → ℝ) : 0 ≤ energy f := by
  exact Finset.sum_nonneg (fun x hx => sq_nonneg (f x))

theorem meanZeroWeight_pos : 0 < meanZeroWeight K := by
  have hq : (1 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K)
  unfold meanZeroWeight
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < Fintype.card K)).2 hq)

def removeCenteredCoordinate (a : K) (f : K → ℝ) (x : K) : ℝ :=
  f x - (f a / meanZeroWeight K) * centeredDelta a x

theorem removeCenteredCoordinate_sum (a : K) (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) :
    (∑ x : K, removeCenteredCoordinate a f x) = 0 := by
  simp only [removeCenteredCoordinate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    centeredDelta_sum, hzero, mul_zero, sub_zero]

theorem removeCenteredCoordinate_self (a : K) (f : K → ℝ) :
    removeCenteredCoordinate a f a = 0 := by
  have hD := (meanZeroWeight_pos (K := K)).ne'
  have hdiag : centeredDelta a a = meanZeroWeight K := by
    simp [centeredDelta, meanZeroWeight]
  unfold removeCenteredCoordinate
  rw [hdiag, div_mul_cancel₀ _ hD, sub_self]

theorem energy_removeCenteredCoordinate (a : K) (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) :
    energy (removeCenteredCoordinate a f) = energy f - f a ^ 2 / meanZeroWeight K := by
  change (∑ x : K, (f x - (f a / meanZeroWeight K) * centeredDelta a x) ^ 2) = _
  rw [energy_sub_centeredDelta f hzero a]
  change energy f - 2 * (f a / meanZeroWeight K) * f a +
    (f a / meanZeroWeight K) ^ 2 * meanZeroWeight K = _
  field_simp [(meanZeroWeight_pos (K := K)).ne']
  ring

theorem coordinate_sq_le_weight_energy (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) (a : K) :
    f a ^ 2 ≤ meanZeroWeight K * energy f := by
  have hnonneg := energy_nonneg (removeCenteredCoordinate a f)
  rw [energy_removeCenteredCoordinate a f hzero] at hnonneg
  have hdiv : f a ^ 2 / meanZeroWeight K ≤ energy f := by linarith
  simpa only [mul_comm] using
    (div_le_iff₀ (meanZeroWeight_pos (K := K))).mp hdiv

theorem transfer_removeCenteredCoordinate_zero
    (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ) (b : K) :
    transfer ψ s (removeCenteredCoordinate 0 f) b =
      transfer ψ s f b - (f 0 / meanZeroWeight K) * centeredDelta 1 b := by
  unfold removeCenteredCoordinate
  rw [transfer_sub, transfer_smul, transfer_centeredDelta_zero ψ hψ s hs]

theorem transfer_scaled_energy
    (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) [CharP K 2] (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ)
    (hzero : (∑ x : K, f x) = 0) :
    meanZeroWeight K * energy (transfer ψ s f) =
      transferScaleSq K s * (meanZeroWeight K * energy f) +
        (1 - transferScaleSq K s) * f 0 ^ 2 := by
  unfold energy
  rw [transfer_sq_sum_of_total_zero ψ hψ s hs f hzero]
  have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold meanZeroWeight transferScaleSq
  field_simp [hq, hs]
  ring

theorem transfer_removeCenteredCoordinate_eval_zero
    (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ) :
    transfer ψ s (removeCenteredCoordinate 0 f) 0 =
      transfer ψ s f 0 + f 0 / ((Fintype.card K : ℝ) - 1) := by
  rw [transfer_removeCenteredCoordinate_zero ψ hψ s hs]
  have hq1 : (1 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K)
  simp only [centeredDelta, zero_ne_one, if_false, zero_sub]
  unfold meanZeroWeight
  field_simp [ne_of_gt (by linarith : (0 : ℝ) < Fintype.card K),
    ne_of_gt (by linarith : (0 : ℝ) < (Fintype.card K : ℝ) - 1)]
  ring

#print axioms transfer_centeredDelta_zero
#print axioms centeredDelta_sq_sum
#print axioms sum_mul_centeredDelta_of_total_zero
#print axioms energy_sub_centeredDelta
#print axioms coordinate_sq_le_weight_energy
#print axioms transfer_removeCenteredCoordinate_zero
#print axioms transfer_scaled_energy
#print axioms transfer_removeCenteredCoordinate_eval_zero

end Carlet.Transfer
