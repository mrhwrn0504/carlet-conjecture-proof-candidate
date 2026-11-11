import Carlet.QuadraticRows
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.GroupWithZero.Units.Basic

noncomputable section

open Polynomial
open scoped BigOperators Ring

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

theorem derivative_product_with_inverses {ι : Type*} (s : Finset ι) (a g : ι → A) (x : A)
    (h : ∀ i ∈ s, (x + a i) * g i = 1) :
    (derivative (∏ i ∈ s, (X + C (a i)))).eval x =
      (∏ i ∈ s, (x + a i)) * ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hinv := h i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, (x + a j) * g j = 1 :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi, derivative_mul, derivative_add, derivative_X,
      derivative_C, add_zero, eval_add, eval_mul, eval_prod, eval_X, eval_C, one_mul,
      ih hs, Finset.sum_insert hi]
    calc
      (∏ j ∈ s, (x + a j)) + (x + a i) * ((∏ j ∈ s, (x + a j)) * ∑ j ∈ s, g j) =
          ((x + a i) * g i) * (∏ j ∈ s, (x + a j)) +
            (x + a i) * ((∏ j ∈ s, (x + a j)) * ∑ j ∈ s, g j) := by rw [hinv, one_mul]
      _ = ((x + a i) * ∏ j ∈ s, (x + a j)) * (g i + ∑ j ∈ s, g j) := by ring

theorem reciprocal_sum_eq_derivative {ι : Type*} (s : Finset ι) (a : ι → A) (x : A)
    (h : ∀ i ∈ s, IsUnit (x + a i)) :
    (∑ i ∈ s, Ring.inverse (x + a i)) =
      (derivative (∏ i ∈ s, (X + C (a i)))).eval x *
        Ring.inverse (∏ i ∈ s, (x + a i)) := by
  have hd := derivative_product_with_inverses s a (fun i => Ring.inverse (x + a i)) x
    (fun i hi => Ring.mul_inverse_cancel _ (h i hi))
  have hp : IsUnit (∏ i ∈ s, (x + a i)) := IsUnit.prod_iff.mpr h
  rw [hd, mul_right_comm]
  rw [Ring.mul_inverse_cancel _ hp, one_mul]

def linearScale (c : ℕ → A) : ℕ → A
  | 0 => 1
  | n+1 => scale c n * linearScale c n

theorem derivative_reconstructed (h2 : (2 : A) = 0) (c : ℕ → A) (n : ℕ) :
    derivative (reconstructedPolynomial c n) = C (linearScale c n) := by
  induction n with
  | zero => simp [reconstructedPolynomial, linearScale]
  | succ n ih =>
    simp only [reconstructedPolynomial, derivative_add, derivative_sq, h2, C_0,
      zero_mul, derivative_mul, derivative_C, ih, zero_add, map_mul, linearScale]

def blockSum (x : ℕ → A) (n : ℕ) : A :=
  ∑ b : Bits n, Ring.inverse (x n + combination x n b)

theorem blockSum_eq_scale_ratio (h2 : (2 : A) = 0) (x c : ℕ → A) (n : ℕ)
    (hdiag : ∀ j ≤ n, (reconstructedPolynomial c j).eval (x j) = scale c j)
    (hunit : ∀ b : Bits n, IsUnit (x n + combination x n b)) :
    blockSum x n = linearScale c n * Ring.inverse (scale c n) := by
  have hpoly : indexedProduct x n = reconstructedPolynomial c n :=
    indexedProduct_eq_reconstructed h2 x c n (fun j hj => hdiag j (Nat.le_of_lt hj))
  rw [blockSum, reciprocal_sum_eq_derivative Finset.univ (combination x n) (x n)
    (fun b hb => hunit b)]
  have hp : (∏ b : Bits n, (x n + combination x n b)) = scale c n := by
    have hval := congrArg (Polynomial.eval (x n)) hpoly
    simpa only [indexedProduct, eval_prod, eval_add, eval_X, eval_C, hdiag n (Nat.le_refl n)] using hval
  change (derivative (indexedProduct x n)).eval (x n) *
    Ring.inverse (∏ b : Bits n, (x n + combination x n b)) = _
  rw [hpoly, derivative_reconstructed h2, eval_C, hp]

#print axioms reciprocal_sum_eq_derivative
#print axioms derivative_reconstructed
#print axioms blockSum_eq_scale_ratio

end Carlet.Quadratic
