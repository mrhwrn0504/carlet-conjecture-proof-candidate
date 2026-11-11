import Carlet.QuadraticPointMap

noncomputable section

open Polynomial
open scoped BigOperators Ring

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

def FullRank (x : ℕ → A) (r : ℕ) : Prop :=
  ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination x r b)

theorem fullRank_down (x : ℕ → A) (n : ℕ) (h : FullRank x (n+1)) : FullRank x n := by
  intro b hb
  have hne : (b, false) ≠ zeroBits (n+1) := by
    intro he
    exact hb (congrArg Prod.fst he)
  simpa [combination] using h (b, false) hne

theorem fullRank_prefix (x : ℕ → A) (r n : ℕ) (hn : n ≤ r)
    (h : FullRank x r) : FullRank x n := by
  revert h
  induction hn with
  | refl => exact id
  | @step m hm ih => intro h; exact ih (fullRank_down x m h)

theorem prefix_coset_isUnit (x : ℕ → A) (r n : ℕ) (hn : n < r)
    (h : FullRank x r) (b : Bits n) : IsUnit (x n + combination x n b) := by
  have hp := fullRank_prefix x r (n+1) (by omega) h
  have hne : (b, true) ≠ zeroBits (n+1) := by
    intro he
    have hs := congrArg Prod.snd he
    cases hs
  simpa [combination, add_comm] using hp (b, true) hne

def delta (x : ℕ → A) (n : ℕ) : A := (kernelPolynomial x n).eval (x n)

theorem delta_isUnit (h2 : (2 : A) = 0) (x : ℕ → A) (r n : ℕ) (hn : n < r)
    (h : FullRank x r) : IsUnit (delta x n) := by
  rw [delta, ← indexedProduct_eq_kernel h2]
  simp only [indexedProduct, eval_prod, eval_add, eval_X, eval_C]
  exact IsUnit.prod_univ_iff.mpr (prefix_coset_isUnit x r n hn h)

def forwardC (x : ℕ → A) (n : ℕ) : A :=
  delta x (n+1) * Ring.inverse (delta x n ^ 2)

theorem forward_scale_eq_delta (h2 : (2 : A) = 0) (x : ℕ → A) (r : ℕ)
    (hx : x 0 = 1) (h : FullRank x r) :
    ∀ n < r, scale (forwardC x) n = delta x n := by
  intro n
  induction n with
  | zero => intro hn; simpa [scale, delta, kernelPolynomial] using hx.symm
  | succ n ih =>
    intro hn
    have hn0 : n < r := by omega
    rw [scale, ih hn0, forwardC, mul_assoc,
      Ring.inverse_mul_cancel _ ((delta_isUnit h2 x r n hn0 h).pow 2), mul_one]

theorem forward_reconstructed_eq_kernel (h2 : (2 : A) = 0) (x : ℕ → A) (r : ℕ)
    (hx : x 0 = 1) (h : FullRank x r) :
    ∀ n ≤ r, reconstructedPolynomial (forwardC x) n = kernelPolynomial x n := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
    intro hn
    have hn0 : n < r := by omega
    rw [reconstructedPolynomial, ih (by omega), forward_scale_eq_delta h2 x r hx h n hn0]
    rfl

theorem forward_scale_isUnit (h2 : (2 : A) = 0) (x : ℕ → A) (r n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (h : FullRank x r) : IsUnit (scale (forwardC x) n) := by
  rw [forward_scale_eq_delta h2 x r hx h n hn]
  exact delta_isUnit h2 x r n hn h

theorem linearScale_isUnit (c : ℕ → A) (n : ℕ)
    (h : ∀ j < n, IsUnit (scale c j)) : IsUnit (linearScale c n) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih =>
    exact (h n (Nat.lt_succ_self n)).mul
      (ih (fun j hj => h j (Nat.lt_succ_of_lt hj)))

def forwardT (x : ℕ → A) (n : ℕ) : A := reciprocalRatio (forwardC x) n

def forwardD (x : ℕ → A) (n : ℕ) : A := Ring.inverse (forwardT x n)

def forwardU (x : ℕ → A) (a j : ℕ) : A :=
  (kernelPolynomial x j).eval (x a) * Ring.inverse (delta x j)

theorem forwardT_isUnit (h2 : (2 : A) = 0) (x : ℕ → A) (r n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (h : FullRank x r) : IsUnit (forwardT x n) := by
  exact (linearScale_isUnit _ n (fun j hj =>
    forward_scale_isUnit h2 x r j (lt_trans hj hn) hx h)).mul
      (forward_scale_isUnit h2 x r n hn hx h).ringInverse

theorem forwardT_eq_blockSum (h2 : (2 : A) = 0) (x : ℕ → A) (r n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (h : FullRank x r) : forwardT x n = blockSum x n := by
  symm
  apply blockSum_eq_scale_ratio h2 x (forwardC x) n
  · intro j hj
    rw [forward_reconstructed_eq_kernel h2 x r hx h j (by omega),
      forward_scale_eq_delta h2 x r hx h j (lt_of_le_of_lt hj hn)]
    rfl
  · exact prefix_coset_isUnit x r n hn h

#print axioms delta_isUnit
#print axioms forward_reconstructed_eq_kernel
#print axioms forwardT_isUnit
#print axioms forwardT_eq_blockSum

end Carlet.Quadratic
