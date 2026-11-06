import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section

open scoped BigOperators

namespace Carlet.Transfer

variable {K : Type*} [Field K] [Fintype K]

def nonzeroElements : Finset K := by classical exact Finset.univ.erase 0

theorem sum_nonzero_char_div (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (v : K) (hv : v ≠ 0) :
    (∑ x ∈ nonzeroElements, ψ (x / v)) = -1 := by
  classical
  have ht : (∑ x : K, ψ (x / v)) = 0 := by
    calc
      _ = ∑ x : K, ψ x := Fintype.sum_equiv (Equiv.divRight₀ v hv) _ _ (fun _ => rfl)
      _ = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
  have h := Finset.sum_erase_add (Finset.univ : Finset K) (fun x => ψ (x / v))
    (Finset.mem_univ 0)
  simpa only [nonzeroElements, zero_div, AddChar.map_zero_eq_one, ht,
    add_eq_zero_iff_eq_neg] using h

theorem sum_nonzero_char_div_left (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (x : K) (hx : x ≠ 0) :
    (∑ v ∈ nonzeroElements, ψ (x / v)) = -1 := by
  classical
  have ht : (∑ v : K, ψ (x / v)) = 0 := by
    calc
      _ = ∑ v : K, ψ v := Fintype.sum_equiv (Equiv.divLeft₀ x hx) _ _ (fun _ => rfl)
      _ = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
  have h := Finset.sum_erase_add (Finset.univ : Finset K) (fun v => ψ (x / v))
    (Finset.mem_univ 0)
  simpa only [nonzeroElements, div_zero, AddChar.map_zero_eq_one, ht,
    add_eq_zero_iff_eq_neg] using h

/-- The unnormalized transfer in the shifted output coordinate x=b-1.
In characteristic two this is the paper's x=b+1. -/
def transferNumerator (ψ : AddChar K ℝ) (s : ℝ) (f : K → ℝ) (x : K) : ℝ := by
  classical
  exact if x = 0 then (Fintype.card K - s) * f 0 else
    ∑ v ∈ nonzeroElements, (1 + (s-1) * ψ (x/v)) * f v

def coreTransfer (ψ : AddChar K ℝ) (s : ℝ) (f : K → ℝ) (x : K) : ℝ :=
  transferNumerator ψ s f x / (Fintype.card K - s)

theorem transferNumerator_uniform (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ) (x : K) :
    transferNumerator ψ s (fun _ => 1) x = Fintype.card K - s := by
  classical
  by_cases hx : x = 0
  · simp [transferNumerator, hx]
  · simp only [transferNumerator, if_neg hx, mul_one, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, sum_nonzero_char_div_left ψ hψ x hx]
    have hn : (nonzeroElements (K := K)).card + 1 = Fintype.card K := by
      exact Finset.card_erase_add_one (Finset.mem_univ 0)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : ((nonzeroElements (K := K)).card : ℝ) + 1 = Fintype.card K := by
      exact_mod_cast hn
    rw [← hc]
    ring

theorem transferNumerator_sum (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ) (f : K → ℝ) :
    (∑ x : K, transferNumerator ψ s f x) =
      (Fintype.card K - s) * ∑ x : K, f x := by
  classical
  have hcol (v : K) (hv : v ∈ nonzeroElements) :
      (∑ x ∈ nonzeroElements, (1+(s-1)*ψ (x/v))*f v) =
        (Fintype.card K - s)*f v := by
    have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_nonzero_char_div ψ hψ v hv0]
    have hn : (nonzeroElements (K := K)).card + 1 = Fintype.card K :=
      Finset.card_erase_add_one (Finset.mem_univ 0)
    have hc : ((nonzeroElements (K := K)).card : ℝ) + 1 = Fintype.card K := by
      exact_mod_cast hn
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← hc]
    ring
  have hz : (∑ x ∈ nonzeroElements, transferNumerator ψ s f x) =
      ∑ x ∈ nonzeroElements, ∑ v ∈ nonzeroElements, (1+(s-1)*ψ (x/v))*f v := by
    apply Finset.sum_congr rfl
    intro x hx
    exact if_neg (Finset.mem_erase.mp hx).1
  have hf := Finset.sum_erase_add (Finset.univ : Finset K) f (Finset.mem_univ 0)
  have ht := Finset.sum_erase_add (Finset.univ : Finset K)
    (transferNumerator ψ s f) (Finset.mem_univ 0)
  rw [← ht]
  change (∑ x ∈ nonzeroElements, transferNumerator ψ s f x) +
    transferNumerator ψ s f 0 = _
  rw [hz, Finset.sum_comm]
  have hcSum : (∑ v ∈ nonzeroElements, ∑ x ∈ nonzeroElements,
      (1+(s-1)*ψ (x/v))*f v) =
      ∑ v ∈ nonzeroElements, (Fintype.card K-s)*f v :=
    Finset.sum_congr rfl hcol
  rw [hcSum]
  rw [← Finset.mul_sum]
  simp only [transferNumerator, ite_true]
  rw [← mul_add]
  exact congrArg ((Fintype.card K - s) * ·) hf

theorem coreTransfer_sum (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ) :
    (∑ x : K, coreTransfer ψ s f x) = ∑ x : K, f x := by
  simp only [coreTransfer, ← Finset.sum_div, transferNumerator_sum ψ hψ]
  exact mul_div_cancel_left₀ _ hs

theorem coreTransfer_uniform (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (x : K) :
    coreTransfer ψ s (fun _ => 1) x = 1 := by
  rw [coreTransfer, transferNumerator_uniform ψ hψ, div_self hs]

theorem transferNumerator_smul (ψ : AddChar K ℝ) (s c : ℝ) (f : K → ℝ) (x : K) :
    transferNumerator ψ s (fun v => c*f v) x = c * transferNumerator ψ s f x := by
  classical
  by_cases hx : x = 0
  · simp only [transferNumerator, if_pos hx]
    ring
  · simp only [transferNumerator, if_neg hx]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring

def transfer (ψ : AddChar K ℝ) (s : ℝ) (f : K → ℝ) (b : K) : ℝ :=
  coreTransfer ψ s f (b-1)

theorem transfer_sum (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (f : K → ℝ) :
    (∑ b : K, transfer ψ s f b) = ∑ b : K, f b := by
  calc
    _ = ∑ x : K, coreTransfer ψ s f x := by
      simpa only [transfer, sub_eq_add_neg] using
        (Fintype.sum_equiv (Equiv.addRight (-1 : K))
          (fun x => coreTransfer ψ s f (x+(-1))) (coreTransfer ψ s f) (fun _ => rfl))
    _ = _ := coreTransfer_sum ψ hψ s hs f

theorem transfer_constant (ψ : AddChar K ℝ) (hψ : ψ ≠ 0) (s c : ℝ)
    (hs : (Fintype.card K : ℝ) - s ≠ 0) (b : K) :
    transfer ψ s (fun _ => c) b = c := by
  change transferNumerator ψ s (fun _ => c) (b-1) / _ = c
  have hc : (fun _ : K => c) = fun _ => c*1 := by simp only [mul_one]
  rw [hc, transferNumerator_smul, transferNumerator_uniform ψ hψ]
  exact mul_div_cancel_right₀ c hs

#print axioms sum_nonzero_char_div
#print axioms transferNumerator_uniform
#print axioms coreTransfer_sum
#print axioms coreTransfer_uniform
#print axioms transfer_sum
#print axioms transfer_constant

end Carlet.Transfer
