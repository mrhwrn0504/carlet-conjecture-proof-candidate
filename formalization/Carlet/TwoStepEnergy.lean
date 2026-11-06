import Carlet.TransferEnergy
import Mathlib.Analysis.Real.Sqrt

noncomputable section

namespace Carlet.Transfer

open scoped BigOperators

/-- A sufficient two-step estimate using only a rank-one energy identity and
one coordinate bound; no spectral decomposition is required. -/
theorem twoStep_rankOne_scalar (A b c x r H : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hAb : A ≤ b ^ 2) (hr : r ^ 2 ≤ A * H) :
    b ^ 2 * (x ^ 2 + A * H) + (1 - b ^ 2) * (-c * x + r) ^ 2 ≤
      (b + c) ^ 2 * (x ^ 2 + H) := by
  have hcoeff : 0 ≤ 1 - b ^ 2 := by nlinarith
  have hrB : r ^ 2 ≤ b ^ 2 * H :=
    hr.trans (mul_le_mul_of_nonneg_right hAb hH)
  have hdiv : r ^ 2 / b ≤ b * H := by
    apply (div_le_iff₀ hb).2
    nlinarith [hrB]
  have hcs : (-c * x + r) ^ 2 ≤ (b + c) * (c * x ^ 2 + r ^ 2 / b) := by
    have hnonneg : 0 ≤ (c / b) * (b * x + r) ^ 2 := by positivity
    have hid : (b + c) * (c * x ^ 2 + r ^ 2 / b) - (-c * x + r) ^ 2 =
        (c / b) * (b * x + r) ^ 2 := by
      field_simp [hb.ne']
      ring
    linarith
  have hcsB : (-c * x + r) ^ 2 ≤ (b + c) * (c * x ^ 2 + b * H) :=
    hcs.trans (mul_le_mul_of_nonneg_left (by linarith [hdiv]) (by linarith))
  have hbase : b ^ 2 * (x ^ 2 + A * H) ≤ b ^ 2 * x ^ 2 + b ^ 4 * H := by
    calc
      _ = b ^ 2 * x ^ 2 + (b ^ 2 * H) * A := by ring
      _ ≤ b ^ 2 * x ^ 2 + (b ^ 2 * H) * b ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hAb
          (mul_nonneg (sq_nonneg b) hH))
      _ = _ := by ring
  have hlast : b ^ 2 * x ^ 2 + b ^ 4 * H +
      (1 - b ^ 2) * ((b + c) * (c * x ^ 2 + b * H)) ≤
        (b + c) ^ 2 * (x ^ 2 + H) := by
    have hid : (b + c) ^ 2 * (x ^ 2 + H) -
        (b ^ 2 * x ^ 2 + b ^ 4 * H +
          (1 - b ^ 2) * ((b + c) * (c * x ^ 2 + b * H))) =
        (b * c * (1 + b ^ 2) + b ^ 2 * c ^ 2) * x ^ 2 +
          (b * c * (1 + b ^ 2) + c ^ 2) * H := by ring
    have hnonneg : 0 ≤ (b * c * (1 + b ^ 2) + b ^ 2 * c ^ 2) * x ^ 2 +
        (b * c * (1 + b ^ 2) + c ^ 2) * H := by positivity
    linarith
  exact (add_le_add hbase (mul_le_mul_of_nonneg_left hcsB hcoeff)).trans hlast

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem twoStep_energy_le (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s t b : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0)
    (ht : (Fintype.card K : ℝ) - t ≠ 0)
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hAb : transferScaleSq K s ≤ b ^ 2)
    (hB : transferScaleSq K t = b ^ 2)
    (f : K → ℝ) (hzero : (∑ x : K, f x) = 0) :
    energy (transfer ψ t (transfer ψ s f)) ≤
      (b + 1 / ((Fintype.card K : ℝ) - 1)) ^ 2 * energy f := by
  let D := meanZeroWeight K
  let A := transferScaleSq K s
  let H := D * energy (removeCenteredCoordinate 0 f)
  let r := transfer ψ s (removeCenteredCoordinate 0 f) 0
  let c := 1 / ((Fintype.card K : ℝ) - 1)
  have hD : 0 < D := meanZeroWeight_pos
  have hH : 0 ≤ H := mul_nonneg hD.le (energy_nonneg _)
  have hc : 0 ≤ c := by
    have hq : (1 : ℝ) < (Fintype.card K : ℝ) := by
      exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K)
    dsimp [c]
    positivity
  have hzrem := removeCenteredCoordinate_sum (0 : K) f hzero
  have hztrans : (∑ x : K, transfer ψ s (removeCenteredCoordinate 0 f) x) = 0 := by
    rw [transfer_sum ψ hψ s hs, hzrem]
  have hr : r ^ 2 ≤ A * H := by
    have hcoord := coordinate_sq_le_weight_energy
      (transfer ψ s (removeCenteredCoordinate 0 f)) hztrans (0 : K)
    rw [transfer_scaled_energy ψ hψ s hs _ hzrem,
      removeCenteredCoordinate_self] at hcoord
    simpa [r, A, H, D, mul_assoc] using hcoord
  have hHidentity : (f 0) ^ 2 + H = D * energy f := by
    dsimp [H]
    rw [energy_removeCenteredCoordinate (0 : K) f hzero]
    change (f 0) ^ 2 + D * (energy f - (f 0) ^ 2 / D) = D * energy f
    field_simp [hD.ne']
    ring
  have hfirst : D * energy (transfer ψ s f) = (f 0) ^ 2 + A * H := by
    have hstep := transfer_scaled_energy ψ hψ s hs f hzero
    change D * energy (transfer ψ s f) = A * (D * energy f) + (1 - A) * f 0 ^ 2 at hstep
    rw [← hHidentity] at hstep
    nlinarith [hstep]
  have hg0 : transfer ψ s f 0 = -c * f 0 + r := by
    have heval := transfer_removeCenteredCoordinate_eval_zero ψ hψ s hs f
    dsimp [r, c]
    rw [div_eq_mul_inv] at heval
    rw [heval]
    simp only [one_div]
    ring
  have hzeroFirst : (∑ x : K, transfer ψ s f x) = 0 := by
    rw [transfer_sum ψ hψ s hs, hzero]
  have hsecond := transfer_scaled_energy ψ hψ t ht (transfer ψ s f) hzeroFirst
  rw [hB, hfirst, hg0] at hsecond
  have hbound := twoStep_rankOne_scalar A b c (f 0) r H hb hb1 hc hH hAb hr
  rw [hHidentity] at hbound
  have hscaled : D * energy (transfer ψ t (transfer ψ s f)) ≤
      D * ((b + c) ^ 2 * energy f) := by
    rw [hsecond]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound
  exact le_of_mul_le_mul_left hscaled hD

/-- The sufficient two-step contraction in the paper's parameter range,
proved directly for the concrete finite-field transfer. -/
theorem twoStep_energy_contraction (ψ : AddChar K ℝ) (hψ : ψ ≠ 0)
    (s t : ℝ) (hs : 2 ≤ s) (ht : 0 < t)
    (htq : t ^ 2 = (Fintype.card K : ℝ))
    (hq : 32 * s ^ 2 ≤ (Fintype.card K : ℝ))
    (f : K → ℝ) (hzero : (∑ x : K, f x) = 0) :
    energy (transfer ψ (2 * s) (transfer ψ s f)) ≤
      (2 * s / t) ^ 2 * energy f := by
  let q : ℝ := Fintype.card K
  let a := t * (s - 1) / (q - s)
  let b := t * (2 * s - 1) / (q - 2 * s)
  have hq32 : 32 * s ^ 2 ≤ q := hq
  have hq128 : 128 ≤ q := by nlinarith [hq32]
  have hdenS : 0 < q - s := by nlinarith [hq32]
  have hden2S : 0 < q - 2 * s := by nlinarith [hq32]
  have ha : 0 ≤ a := div_nonneg (mul_nonneg ht.le (by linarith)) hdenS.le
  have hb : 0 < b := div_pos (mul_pos ht (by linarith)) hden2S
  have hb1 : b ≤ 1 := by
    exact oneStep_scalar_nonexpansive q (2 * s) t (by linarith)
      (by nlinarith [hq32]) (by linarith) ht htq
  have hrat : (s - 1) / (q - s) ≤ (2 * s - 1) / (q - 2 * s) := by
    apply (div_le_div_iff₀ hdenS hden2S).2
    have hprod : 0 ≤ s * (q - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hab : a ≤ b := by
    dsimp [a, b]
    simp only [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hrat ht.le
  have habsq : a ^ 2 ≤ b ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hab) (by linarith : 0 ≤ b + a)
    nlinarith [hprod]
  have hA : transferScaleSq K s = a ^ 2 := by
    dsimp [transferScaleSq, a, q]
    rw [div_pow, mul_pow, htq]
  have hB : transferScaleSq K (2 * s) = b ^ 2 := by
    dsimp [transferScaleSq, b, q]
    rw [div_pow, mul_pow, htq]
  have hbound := twoStep_energy_le ψ hψ s (2 * s) b hdenS.ne' hden2S.ne'
    hb hb1 (by rw [hA]; exact habsq) hB f hzero
  have hscalar : b + 1 / (q - 1) < 2 * s / t :=
    twoStep_scalar_bound q s t hs ht htq hq32
  have hc : 0 ≤ 1 / (q - 1) := div_nonneg zero_le_one (by linarith)
  have hcoef : (b + 1 / (q - 1)) ^ 2 ≤ (2 * s / t) ^ 2 := by
    have hprod : 0 ≤ (2 * s / t - (b + 1 / (q - 1))) *
        (2 * s / t + (b + 1 / (q - 1))) := by
      apply mul_nonneg
      · linarith
      · positivity
    nlinarith [hprod]
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonneg f))

theorem oneStep_energy_nonexpansive (ψ : AddChar K ℝ) (hψ : ψ ≠ 0)
    (s t : ℝ) (hs : 1 ≤ s) (hsq : s ^ 2 ≤ (Fintype.card K : ℝ))
    (hsqStrict : s < (Fintype.card K : ℝ)) (ht : 0 < t)
    (htq : t ^ 2 = (Fintype.card K : ℝ))
    (f : K → ℝ) (hzero : (∑ x : K, f x) = 0) :
    energy (transfer ψ s f) ≤ energy f := by
  have hden : 0 < (Fintype.card K : ℝ) - s := by linarith
  let a := t * (s - 1) / ((Fintype.card K : ℝ) - s)
  have ha : 0 ≤ a := div_nonneg (mul_nonneg ht.le (by linarith)) hden.le
  have ha1 : a ≤ 1 :=
    oneStep_scalar_nonexpansive (Fintype.card K : ℝ) s t hs hsq hsqStrict ht htq
  have hA : transferScaleSq K s = a ^ 2 := by
    dsimp [transferScaleSq, a]
    rw [div_pow, mul_pow, htq]
  have hA1 : transferScaleSq K s ≤ 1 := by rw [hA]; nlinarith
  have hcoord := coordinate_sq_le_weight_energy f hzero (0 : K)
  have hbound : meanZeroWeight K * energy (transfer ψ s f) ≤
      meanZeroWeight K * energy f := by
    rw [transfer_scaled_energy ψ hψ s hden.ne' f hzero]
    calc
      _ ≤ transferScaleSq K s * (meanZeroWeight K * energy f) +
          (1 - transferScaleSq K s) * (meanZeroWeight K * energy f) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcoord (by linarith))
      _ = _ := by ring
  exact le_of_mul_le_mul_left hbound (meanZeroWeight_pos (K := K))

/-- A square-root-free energy factor, convenient for iterating the actual
probability recurrence using only integer powers. -/
theorem twoStep_energy_contraction_card (ψ : AddChar K ℝ) (hψ : ψ ≠ 0)
    (s : ℝ) (hs : 2 ≤ s) (hq : 32 * s ^ 2 ≤ (Fintype.card K : ℝ))
    (f : K → ℝ) (hzero : (∑ x : K, f x) = 0) :
    energy (transfer ψ (2 * s) (transfer ψ s f)) ≤
      (4 * s ^ 2 / (Fintype.card K : ℝ)) * energy f := by
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have ht : 0 < Real.sqrt (Fintype.card K : ℝ) := Real.sqrt_pos.mpr hqpos
  have htq := Real.sq_sqrt hqpos.le
  have hbound := twoStep_energy_contraction ψ hψ s (Real.sqrt (Fintype.card K : ℝ))
    hs ht htq hq f hzero
  have hcoef : (2 * s / Real.sqrt (Fintype.card K : ℝ)) ^ 2 =
      4 * s ^ 2 / (Fintype.card K : ℝ) := by
    rw [div_pow, mul_pow, htq]
    ring
  rw [hcoef] at hbound
  exact hbound

#print axioms twoStep_rankOne_scalar
#print axioms twoStep_energy_le
#print axioms twoStep_energy_contraction
#print axioms oneStep_energy_nonexpansive
#print axioms twoStep_energy_contraction_card

end Carlet.Transfer
