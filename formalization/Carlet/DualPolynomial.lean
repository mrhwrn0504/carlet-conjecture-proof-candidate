import Carlet.NextCoefficient

noncomputable section

open Polynomial
open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

theorem trace_pow_two (x : K) (n : ℕ) :
    Algebra.trace (ZMod 2) K (x^(2^n)) = Algebra.trace (ZMod 2) K x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, trace_square, ih]

theorem pow_two_surjective (n : ℕ) : Function.Surjective (fun x : K => x^(2^n)) := by
  have h := ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K)^n).surjective
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    ZMod.card] using h

def dualPolynomial (c : ℕ → K) (d : ℕ) : K[X] :=
  ∑ i ∈ Finset.range (d+1), C ((c i)^(2^(d-i))) * X^(2^(d-i))

theorem trace_twisted_term (c x y : K) (d i : ℕ) (hi : i ≤ d) :
    Algebra.trace (ZMod 2) K (c*x^(2^i)*y) =
      Algebra.trace (ZMod 2) K (x^(2^d)*((c*y)^(2^(d-i)))) := by
  calc
    _ = Algebra.trace (ZMod 2) K ((c*x^(2^i)*y)^(2^(d-i))) :=
      (trace_pow_two _ _).symm
    _ = _ := by
      congr 1
      rw [mul_pow, mul_pow, ← pow_mul, ← Nat.pow_add,
        show i+(d-i)=d by omega, mul_pow]
      ring

theorem trace_dualPolynomial (c : ℕ → K) (d : ℕ) (x y : K) :
    Algebra.trace (ZMod 2) K ((∑ i ∈ Finset.range (d+1), c i*x^(2^i))*y) =
      Algebra.trace (ZMod 2) K (x^(2^d)*(dualPolynomial c d).eval y) := by
  simp only [dualPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [mul_pow] using trace_twisted_term (c i) x y d i (by
    have := Finset.mem_range.mp hi
    omega)

theorem dualPolynomial_eval_zero_iff (c : ℕ → K) (d : ℕ) (y : K) :
    (dualPolynomial c d).eval y = 0 ↔
      ∀ x : K, Algebra.trace (ZMod 2) K
        ((∑ i ∈ Finset.range (d+1), c i*x^(2^i))*y) = 0 := by
  constructor
  · intro h x
    rw [trace_dualPolynomial, h, mul_zero, map_zero]
  · intro h
    apply (traceForm_nondegenerate (ZMod 2) K).1 ((dualPolynomial c d).eval y)
    intro z
    obtain ⟨x,hx⟩ := pow_two_surjective (K := K) d z
    dsimp only at hx
    have ht := h x
    rw [trace_dualPolynomial, hx] at ht
    change Algebra.trace (ZMod 2) K ((dualPolynomial c d).eval y*z) = 0
    simpa only [mul_comm] using ht

variable [DecidableEq K]

def subspaceDualPolynomial (E : Submodule (ZMod 2) K) : K[X] :=
  dualPolynomial (fun i => (rootProduct (underlyingFinset E)).coeff (2^i))
    (Module.finrank (ZMod 2) E)

theorem subspacePolynomial_eval_frobeniusSum (E : Submodule (ZMod 2) K) (x : K) :
    (rootProduct (underlyingFinset E)).eval x =
      ∑ i ∈ Finset.range (Module.finrank (ZMod 2) E+1),
        (rootProduct (underlyingFinset E)).coeff (2^i)*x^(2^i) := by
  conv_lhs => rw [frobeniusSupported_eq_sum _ (subspacePolynomial_frobeniusSupported E)
    _ (subspacePolynomial_natDegree_pow E).le]
  simp only [eval_finsetSum, eval_monomial]

theorem subspaceDualPolynomial_eval_zero_iff (E : Submodule (ZMod 2) K) (y : K) :
    (subspaceDualPolynomial E).eval y = 0 ↔ y ∈ dualImageEquiv E := by
  rw [subspaceDualPolynomial, dualPolynomial_eval_zero_iff]
  simp_rw [← subspacePolynomial_eval_frobeniusSum]
  change (∀ x : K, Algebra.trace (ZMod 2) K ((rootProduct (underlyingFinset E)).eval x*y) = 0) ↔
    y ∈ (Algebra.traceForm (ZMod 2) K).orthogonal (imageSubspace E)
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h z hz
    obtain ⟨x,rfl⟩ := hz
    exact h x
  · intro h x
    exact h _ ⟨x,rfl⟩

#print axioms trace_pow_two
#print axioms trace_dualPolynomial
#print axioms subspaceDualPolynomial_eval_zero_iff

end Carlet
