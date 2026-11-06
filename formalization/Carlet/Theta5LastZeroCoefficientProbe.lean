import Carlet.Theta5LastCoordinateExpansionProbe
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic

noncomputable section
open Polynomial MvPolynomial
namespace Carlet

local instance t5LastRingCharTwo : CharP (MvPolynomial Theta5Index (ZMod 2)) 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* MvPolynomial Theta5Index (ZMod 2))
    exact MvPolynomial.C_injective _ _) 2

lemma t5Last_coeff_square (p : Polynomial (MvPolynomial Theta5Index (ZMod 2))) (j : ℕ) :
    (p ^ 2).coeff (2^(j+1)) = (p.coeff (2^j))^2 := by
  rw [← map_frobenius_expand 2 p, Polynomial.coeff_map,
    Polynomial.coeff_expand (by decide)]
  have hd : 2 ∣ 2^(j+1) := by
    refine ⟨2^j, ?_⟩
    rw [pow_succ]
    omega
  have hdiv : 2^(j+1) / 2 = 2^j := by
    rw [pow_succ]
    simp
  simp [hd, hdiv, frobenius_def]

lemma t5Last_coeff_extension (p : Polynomial (MvPolynomial Theta5Index (ZMod 2)))
    (c : MvPolynomial Theta5Index (ZMod 2)) (j : ℕ) :
    (p ^ 2 + Polynomial.C c * p).coeff (2^(j+1)) =
      (p.coeff (2^j))^2 + c * p.coeff (2^(j+1)) := by
  rw [Polynomial.coeff_add, t5Last_coeff_square]
  simp [Polynomial.coeff_C_mul, pow_succ]

lemma t5Last_coeff4_P2 : t5EvalP2.coeff 4 = 1 := by
  have h := t5Last_coeff_extension t5EvalP1 (t5EvalP1.eval (t5EvalX 1)) 1
  have he : 2 ^ (1 + 1) = 4 := by norm_num
  have he' : 2 ^ 1 = 2 := by norm_num
  rw [he, he'] at h
  simpa [t5EvalP2, t5EvalP1] using h

lemma t5Last_coeff8_P2 : t5EvalP2.coeff 8 = 0 := by
  have h := t5Last_coeff_extension t5EvalP1 (t5EvalP1.eval (t5EvalX 1)) 2
  have he : 2 ^ (2 + 1) = 8 := by norm_num
  have he' : 2 ^ 2 = 4 := by norm_num
  rw [he, he'] at h
  simpa [t5EvalP2, t5EvalP1] using h

lemma t5Last_coeff2_P1 : t5EvalP1.coeff 2 = 1 := by
  simp [t5EvalP1]

lemma t5Last_coeff2_P2 :
    t5EvalP2.coeff 2 = t5EvalX 0 ^ 2 + t5EvalP1.eval (t5EvalX 1) := by
  have h := t5Last_coeff_extension t5EvalP1 (t5EvalP1.eval (t5EvalX 1)) 0
  have he : 2 ^ (0 + 1) = 2 := by norm_num
  have he' : 2 ^ 0 = 1 := by norm_num
  have hcoeff1 : t5EvalP1.coeff 1 = t5EvalX 0 := by simp [t5EvalP1]
  rw [he, he'] at h
  simpa [t5EvalP2, hcoeff1, t5Last_coeff2_P1] using h

lemma t5Last_coeff8_P3 : t5EvalP3.coeff 8 = 1 := by
  have h := t5Last_coeff_extension t5EvalP2 (t5EvalP2.eval (t5EvalX 2)) 2
  have he : 2 ^ (2 + 1) = 8 := by norm_num
  have he' : 2 ^ 2 = 4 := by norm_num
  rw [he, he'] at h
  simpa [t5EvalP3, t5Last_coeff4_P2, t5Last_coeff8_P2] using h

lemma t5Last_coeff4_P3 :
    t5EvalP3.coeff 4 = (t5EvalP2.coeff 2)^2 + t5EvalP2.eval (t5EvalX 2) := by
  have h := t5Last_coeff_extension t5EvalP2 (t5EvalP2.eval (t5EvalX 2)) 1
  have he : 2 ^ (1 + 1) = 4 := by norm_num
  have he' : 2 ^ 1 = 2 := by norm_num
  rw [he, he'] at h
  simpa [t5EvalP3, t5Last_coeff4_P2] using h

lemma t5Last_coeff8_P4 :
    t5EvalP4.coeff 8 = (t5EvalP3.coeff 4)^2 + t5EvalP3.eval (t5EvalX 3) := by
  have h := t5Last_coeff_extension t5EvalP3 (t5EvalP3.eval (t5EvalX 3)) 2
  have he : 2 ^ (2 + 1) = 8 := by norm_num
  have he' : 2 ^ 2 = 4 := by norm_num
  rw [he, he'] at h
  simpa [t5EvalP4, t5Last_coeff8_P3] using h

lemma t5_even_zmod_zero (n : ℕ) (hn : Even n) : (n : ZMod 2) = 0 := by
  rcases hn with ⟨m, rfl⟩
  push_cast
  have h : (2 : ZMod 2) = 0 := by decide
  calc
    (m : ZMod 2) + (m : ZMod 2) = (2 : ZMod 2) * (m : ZMod 2) := by ring
    _ = 0 := by rw [h]; simp

lemma t5_odd_zmod_one (n : ℕ) (hn : Odd n) : (n : ZMod 2) = 1 := by
  rcases hn with ⟨m, rfl⟩
  push_cast
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h]
  ring

lemma t5_odd_mv_natCast_one (n : ℕ) (hn : Odd n) :
    (n : MvPolynomial Theta5Index (ZMod 2)) = 1 := by
  change MvPolynomial.C (n : ZMod 2) = MvPolynomial.C 1
  rw [t5_odd_zmod_one n hn]
lemma t5_even_mv_natCast_zero (n : ℕ) (hn : Even n) :
    (n : MvPolynomial Theta5Index (ZMod 2)) = 0 := by
  change MvPolynomial.C (n : ZMod 2) = 0
  rw [t5_even_zmod_zero n hn]
  simp

lemma t5_even_mv_scalar_mul_zero (n : ℕ) (hn : Even n)
    (p : MvPolynomial Theta5Index (ZMod 2)) :
    (n : MvPolynomial Theta5Index (ZMod 2)) * p = 0 := by
  rw [t5_even_mv_natCast_zero n hn]
  simp

#print axioms t5_odd_zmod_one
#print axioms t5_odd_mv_natCast_one
#print axioms t5_even_zmod_zero
#print axioms t5_even_mv_natCast_zero
#print axioms t5_even_mv_scalar_mul_zero
end Carlet



