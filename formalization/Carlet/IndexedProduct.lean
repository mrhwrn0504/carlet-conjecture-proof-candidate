import Carlet.QuadraticReconstruction
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Polynomial.BigOperators

/-!
Formal products indexed by binary coefficient vectors. The recursive
vector type retains multiplicities even when the ring-valued sums collide.
No field or reducedness assumption is used.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Carlet.Quadratic

def Bits : ℕ → Type
  | 0 => PUnit
  | n+1 => Bits n × Bool

instance bitsFintype (n : ℕ) : Fintype (Bits n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Bits n × Bool))

def zeroBits : (n : ℕ) → Bits n
  | 0 => PUnit.unit
  | n+1 => (zeroBits n, false)

variable {A : Type*} [CommRing A]

def combination (x : ℕ → A) : (n : ℕ) → Bits n → A
  | 0, _ => 0
  | n+1, b => combination x n b.1 + if b.2 then x n else 0

def indexedProduct (x : ℕ → A) (n : ℕ) : A[X] :=
  ∏ b : Bits n, (X + C (combination x n b))

def kernelPolynomial (x : ℕ → A) : ℕ → A[X]
  | 0 => X
  | n+1 => kernelPolynomial x n ^ 2 + C ((kernelPolynomial x n).eval (x n)) * kernelPolynomial x n

def PolynomialTranslation (p : A[X]) : Prop :=
  ∀ v : A, p.comp (X + C v) = p + C (p.eval v)

theorem square_add_of_two_zero (h2 : (2 : A) = 0) (p q : A[X]) :
    (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
  have hp2 : (2 : A[X]) = 0 := by simpa only [C_ofNat, C_0] using congrArg (C : A →+* A[X]) h2
  rw [add_sq, hp2]
  ring

theorem polynomialTranslation_step (h2 : (2 : A) = 0) (p : A[X]) (c : A)
    (hp : PolynomialTranslation p) : PolynomialTranslation (p ^ 2 + C c * p) := by
  intro v
  simp only [add_comp, pow_comp, mul_comp, C_comp, hp v, eval_add, eval_pow,
    eval_mul, eval_C, map_add, map_mul, map_pow]
  rw [square_add_of_two_zero h2]
  ring

theorem kernelPolynomial_translation (h2 : (2 : A) = 0) (x : ℕ → A) (n : ℕ) :
    PolynomialTranslation (kernelPolynomial x n) := by
  induction n with
  | zero => intro v; simp [kernelPolynomial]
  | succ n ih => exact polynomialTranslation_step h2 _ _ ih

theorem indexedProduct_step (x : ℕ → A) (n : ℕ) :
    indexedProduct x (n+1) =
      indexedProduct x n * (indexedProduct x n).comp (X + C (x n)) := by
  have ht : (∏ b : Bits n, (X + C (combination x n b + x n))) =
      (indexedProduct x n).comp (X + C (x n)) := by
    rw [indexedProduct, Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro b hb
    simp only [add_comp, X_comp, C_comp, map_add]
    ring
  change (∏ b : Bits n × Bool,
    (X + C (combination x n b.1 + if b.2 then x n else 0))) = _
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool, Bool.false_eq_true, ite_true, ite_false, add_zero]
  rw [Finset.prod_mul_distrib, ht]
  change (indexedProduct x n).comp (X + C (x n)) * indexedProduct x n = _
  exact mul_comm _ _

/-- Equality with the actual indexed product, valid even if sums collide. -/
theorem indexedProduct_eq_kernel (h2 : (2 : A) = 0) (x : ℕ → A) (n : ℕ) :
    indexedProduct x n = kernelPolynomial x n := by
  induction n with
  | zero =>
    simp only [indexedProduct, combination, map_zero, add_zero, Finset.prod_const, kernelPolynomial]
    change (X : A[X]) ^ 1 = X
    exact pow_one X
  | succ n ih =>
    rw [indexedProduct_step, ih, kernelPolynomial_translation h2 x n (x n)]
    simp only [kernelPolynomial]
    ring

theorem kernelPolynomial_eq_reconstructed (x c : ℕ → A) (n : ℕ)
    (h : ∀ j < n, (reconstructedPolynomial c j).eval (x j) = scale c j) :
    kernelPolynomial x n = reconstructedPolynomial c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    simp only [kernelPolynomial, reconstructedPolynomial, hi, h n (Nat.lt_succ_self n)]

theorem indexedProduct_eq_reconstructed (h2 : (2 : A) = 0) (x c : ℕ → A) (n : ℕ)
    (h : ∀ j < n, (reconstructedPolynomial c j).eval (x j) = scale c j) :
    indexedProduct x n = reconstructedPolynomial c n := by
  rw [indexedProduct_eq_kernel h2, kernelPolynomial_eq_reconstructed x c n h]

theorem combination_zeroBits (x : ℕ → A) (n : ℕ) : combination x n (zeroBits n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [combination, zeroBits, ih]

theorem translated_combination_isUnit (x : ℕ → A) (n : ℕ)
    (h : IsUnit ((indexedProduct x n).eval (x n))) (b : Bits n) :
    IsUnit (combination x n b + x n) := by
  have hp : IsUnit (∏ a : Bits n, (x n + combination x n a)) := by
    simpa only [indexedProduct, eval_prod, eval_add, eval_X, eval_C] using h
  simpa only [add_comm] using factor_isUnit Finset.univ _ hp b (Finset.mem_univ b)

/-- The Drinfeld-open unit condition, stated for all nonzero binary
coefficient vectors rather than merely for field-valued independent points. -/
theorem all_nonzero_combinations_isUnit (x : ℕ → A) (r : ℕ)
    (h : ∀ j < r, IsUnit ((indexedProduct x j).eval (x j))) :
    ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination x r b) := by
  induction r with
  | zero => intro b hb; cases b; exact False.elim (hb rfl)
  | succ n ih =>
    intro b hb
    rcases b with ⟨a, flag⟩
    cases flag with
    | false =>
      have ha : a ≠ zeroBits n := by intro he; apply hb; subst a; rfl
      simpa [combination] using
        ih (fun j hj => h j (Nat.lt_succ_of_lt hj)) a ha
    | true =>
      simpa [combination] using
        translated_combination_isUnit x n (h n (Nat.lt_succ_self n)) a

#print axioms indexedProduct_eq_kernel
#print axioms indexedProduct_eq_reconstructed
#print axioms all_nonzero_combinations_isUnit

end Carlet.Quadratic
