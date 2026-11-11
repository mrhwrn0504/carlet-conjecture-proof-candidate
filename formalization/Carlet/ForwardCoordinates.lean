import Carlet.ForwardScales

noncomputable section

open Polynomial
open scoped BigOperators Ring

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

theorem ring_inverse_sq (a : A) (ha : IsUnit a) :
    Ring.inverse (a ^ 2) = Ring.inverse a ^ 2 := by
  simpa only [pow_two] using (Ring.inverse_mul (a := a) (b := a) (Or.inl ha))

theorem normalized_artinSchreier (y d e : A) (hd : IsUnit d) (he : IsUnit e) :
    (y * Ring.inverse d) ^ 2 + y * Ring.inverse d =
      (e * Ring.inverse (d ^ 2)) * ((y ^ 2 + d * y) * Ring.inverse e) := by
  rw [ring_inverse_sq d hd]
  have hdi := Ring.mul_inverse_cancel d hd
  have hei := Ring.mul_inverse_cancel e he
  calc
    _ = y ^ 2 * Ring.inverse d ^ 2 + (y * Ring.inverse d) * (d * Ring.inverse d) := by
      rw [hdi, mul_one]; ring
    _ = (y ^ 2 + d * y) * Ring.inverse d ^ 2 := by ring
    _ = ((y ^ 2 + d * y) * Ring.inverse d ^ 2) * (e * Ring.inverse e) := by
      rw [hei, mul_one]
    _ = _ := by ring

theorem forwardU_diagonal (h2 : (2 : A) = 0) (x : ℕ → A) (r a : ℕ) (ha : a < r)
    (h : FullRank x r) : forwardU x a a = 1 := by
  exact Ring.mul_inverse_cancel (delta x a) (delta_isUnit h2 x r a ha h)

theorem forwardU_relation (h2 : (2 : A) = 0) (x : ℕ → A) (r : ℕ)
    (h : FullRank x r) (a j : ℕ) (ha : a < r) (hj : j < a) :
    forwardU x a j ^ 2 + forwardU x a j = forwardC x j * forwardU x a (j+1) := by
  have hj0 : j < r := lt_trans hj ha
  have hj1 : j+1 < r := by omega
  have hp : (kernelPolynomial x (j+1)).eval (x a) =
      (kernelPolynomial x j).eval (x a) ^ 2 + delta x j * (kernelPolynomial x j).eval (x a) := by
    simp only [kernelPolynomial, eval_add, eval_pow, eval_mul, eval_C, delta]
  simp only [forwardU, forwardC, hp]
  exact normalized_artinSchreier _ _ _ (delta_isUnit h2 x r j hj0 h)
    (delta_isUnit h2 x r (j+1) hj1 h)

theorem forward_triangularRelations (h2 : (2 : A) = 0) (x : ℕ → A) (r : ℕ)
    (h : FullRank x r) : TriangularRelations (forwardC x) (forwardU x) r :=
  ⟨fun a ha => forwardU_diagonal h2 x r a ha h,
    fun a ha j hj => forwardU_relation h2 x r h a j ha hj⟩

theorem forwardU_zero (x : ℕ → A) (hx : x 0 = 1) (a : ℕ) : forwardU x a 0 = x a := by
  simp [forwardU, kernelPolynomial, delta, hx]

theorem forwardT_zero (x : ℕ → A) : forwardT x 0 = 1 := by
  simp [forwardT, reciprocalRatio, linearScale, scale]

theorem forward_inverse_relation (h2 : (2 : A) = 0) (x : ℕ → A) (r n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (h : FullRank x r) : forwardT x n * forwardD x n = 1 :=
  Ring.mul_inverse_cancel _ (forwardT_isUnit h2 x r n hn hx h)

theorem forward_ratio_relation (h2 : (2 : A) = 0) (x : ℕ → A) (r n : ℕ) (hn : n+1 < r)
    (hx : x 0 = 1) (h : FullRank x r) :
    forwardC x n * forwardT x (n+1) = forwardT x n := by
  exact reciprocalRatio_step _ n
    (forward_scale_isUnit h2 x r n (by omega) hx h)
    (forward_scale_isUnit h2 x r (n+1) hn hx h)

def QuadraticCondition (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ) : Prop :=
  TriangularRelations c u r ∧ t 0 = 1 ∧
  (∀ j < r, t j * d j = 1) ∧
  (∀ j, j+1 < r → c j * t (j+1) = t j) ∧
  (∑ j ∈ Finset.range r, t j) = 0

theorem forward_satisfies_quadratic [Algebra (ZMod 2) A] (x : ℕ → A) (r : ℕ)
    (h : OpenCarletCondition x r) :
    QuadraticCondition (forwardC x) (forwardT x) (forwardD x) (forwardU x) r := by
  refine ⟨forward_triangularRelations algebra_two_eq_zero x r h.2.1, forwardT_zero x,
    (fun j hj => forward_inverse_relation algebra_two_eq_zero x r j hj h.1 h.2.1),
    (fun j hj => forward_ratio_relation algebra_two_eq_zero x r j hj h.1 h.2.1), ?_⟩
  calc
    _ = ∑ j ∈ Finset.range r, blockSum x j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact forwardT_eq_blockSum algebra_two_eq_zero x r j (Finset.mem_range.mp hj) h.1 h.2.1
    _ = fullReciprocalSum x r := (fullReciprocalSum_eq_blocks x r).symm
    _ = 0 := h.2.2

theorem forward_then_reverse (x : ℕ → A) (hx : x 0 = 1) :
    (fun a => forwardU x a 0) = x := by
  funext a
  exact forwardU_zero x hx a

#print axioms forward_triangularRelations
#print axioms forward_satisfies_quadratic
#print axioms forward_then_reverse

end Carlet.Quadratic
