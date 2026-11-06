import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Elementary algebra for the Carlet manuscript.
The finite product is the actual product of X + a. No geometric assumption
or conjectural hypothesis is introduced here.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Carlet

variable {K : Type*} [Field K]

def rootProduct (s : Finset K) : K[X] := ∏ a ∈ s, (X + C a)

theorem rootProduct_coeff_zero (s : Finset K) :
    (rootProduct s).coeff 0 = ∏ a ∈ s, a := by
  classical
  simp [rootProduct, Polynomial.coeff_zero_prod]

theorem rootProduct_coeff_one (s : Finset K) (hs : ∀ a ∈ s, a ≠ 0) :
    (rootProduct s).coeff 1 = (∏ a ∈ s, a) * ∑ a ∈ s, a⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootProduct, Polynomial.coeff_one]
  | @insert a s ha ih =>
    have hane : a ≠ 0 := hs a (Finset.mem_insert_self a s)
    have hsn : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (Finset.mem_insert_of_mem hb)
    have hp : rootProduct (insert a s) = (X + C a) * rootProduct s := by
      simp [rootProduct, ha]
    rw [hp, Polynomial.mul_coeff_one, rootProduct_coeff_zero, ih hsn]
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, coeff_X_one,
      coeff_C_succ, add_zero, one_mul, Finset.prod_insert ha, Finset.sum_insert ha]
    field_simp
    ring

variable [DecidableEq K]

def nonzeroRootProduct (s : Finset K) : K[X] := rootProduct (s.erase 0)

theorem nonzeroRootProduct_coeff_zero_ne (s : Finset K) :
    (nonzeroRootProduct s).coeff 0 ≠ 0 := by
  classical
  rw [nonzeroRootProduct, rootProduct_coeff_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => (Finset.mem_erase.mp ha).1)

theorem inverse_sum_eq_coeff_ratio (s : Finset K) :
    (∑ a ∈ s.erase 0, a⁻¹) =
      (nonzeroRootProduct s).coeff 1 / (nonzeroRootProduct s).coeff 0 := by
  classical
  have hs : ∀ a ∈ s.erase 0, a ≠ 0 := fun a ha => (Finset.mem_erase.mp ha).1
  have hp : (∏ a ∈ s.erase 0, a) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
  rw [nonzeroRootProduct, rootProduct_coeff_one _ hs, rootProduct_coeff_zero]
  field_simp

theorem inverse_sum_eq_zero_iff (s : Finset K) :
    (∑ a ∈ s.erase 0, a⁻¹) = 0 ↔ (nonzeroRootProduct s).coeff 1 = 0 := by
  rw [inverse_sum_eq_coeff_ratio, div_eq_zero_iff]
  simp [nonzeroRootProduct_coeff_zero_ne]

theorem rootProduct_eq_X_mul_nonzeroRootProduct (s : Finset K) (h0 : 0 ∈ s) :
    rootProduct s = X * nonzeroRootProduct s := by
  classical
  calc
    rootProduct s = rootProduct (insert 0 (s.erase 0)) := by
      rw [Finset.insert_erase h0]
    _ = X * nonzeroRootProduct s := by
      simp [rootProduct, nonzeroRootProduct]

/-- The manuscript's c₁/c₀ formula, where c₀=[X]L and c₁=[X²]L.
It is proved for any finite set containing zero, hence applies to subspaces. -/
theorem inverse_sum_eq_rootProduct_coeff_ratio (s : Finset K) (h0 : 0 ∈ s) :
    (∑ a ∈ s.erase 0, a⁻¹) = (rootProduct s).coeff 2 / (rootProduct s).coeff 1 := by
  rw [rootProduct_eq_X_mul_nonzeroRootProduct s h0]
  simpa only [Polynomial.coeff_X_mul] using inverse_sum_eq_coeff_ratio s

theorem rootProduct_coeff_one_ne (s : Finset K) (h0 : 0 ∈ s) :
    (rootProduct s).coeff 1 ≠ 0 := by
  rw [rootProduct_eq_X_mul_nonzeroRootProduct s h0, Polynomial.coeff_X_mul]
  exact nonzeroRootProduct_coeff_zero_ne s

theorem inverse_sum_eq_zero_iff_rootProduct_coeff_two (s : Finset K) (h0 : 0 ∈ s) :
    (∑ a ∈ s.erase 0, a⁻¹) = 0 ↔ (rootProduct s).coeff 2 = 0 := by
  rw [inverse_sum_eq_rootProduct_coeff_ratio s h0, div_eq_zero_iff]
  simp [rootProduct_coeff_one_ne s h0]

omit [DecidableEq K] in
/-- The X² coefficient calculation used in the manuscript's extension step. -/
theorem extension_coeff_two (L : K[X]) (a : K) (hL : L.coeff 0 = 0) :
    (L ^ 2 + C a * L).coeff 2 = L.coeff 1 ^ 2 + a * L.coeff 2 := by
  simp [pow_two, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ,
    hL]

omit [DecidableEq K] in
theorem extension_coeff_two_eq_zero_iff (L : K[X]) (a : K)
    (hL : L.coeff 0 = 0) (h1 : L.coeff 2 ≠ 0) :
    (L ^ 2 + C a * L).coeff 2 = 0 ↔ a = -(L.coeff 1 ^ 2) / L.coeff 2 := by
  rw [extension_coeff_two L a hL]
  constructor
  · intro h
    apply (eq_div_iff h1).2
    exact eq_neg_of_add_eq_zero_right h
  · intro h
    rw [h]
    field_simp
    ring

omit [DecidableEq K] in
theorem extension_coeff_two_eq_zero_iff_char_two [CharP K 2] (L : K[X]) (a : K)
    (hL : L.coeff 0 = 0) (h1 : L.coeff 2 ≠ 0) :
    (L ^ 2 + C a * L).coeff 2 = 0 ↔ a = (L.coeff 1 ^ 2) / L.coeff 2 := by
  simpa only [CharTwo.neg_eq] using extension_coeff_two_eq_zero_iff L a hL h1

#print axioms rootProduct_coeff_one
#print axioms inverse_sum_eq_coeff_ratio
#print axioms inverse_sum_eq_zero_iff
#print axioms inverse_sum_eq_rootProduct_coeff_ratio
#print axioms inverse_sum_eq_zero_iff_rootProduct_coeff_two
#print axioms extension_coeff_two
#print axioms extension_coeff_two_eq_zero_iff
#print axioms extension_coeff_two_eq_zero_iff_char_two

end Carlet
