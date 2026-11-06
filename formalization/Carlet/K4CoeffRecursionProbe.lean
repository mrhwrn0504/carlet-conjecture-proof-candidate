import Carlet.K4ThetaProbe
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring

set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
open Polynomial MvPolynomial
namespace Carlet

abbrev K4FreeIndex := Fin 4
abbrev K4FreeRing := MvPolynomial K4FreeIndex (ZMod 2)

def k4UniversalX (i : K4FreeIndex) : K4FreeRing := MvPolynomial.X i

def k4UniversalP1 : Polynomial K4FreeRing :=
  Polynomial.X^2 + Polynomial.C (k4UniversalX 0) * Polynomial.X

def k4UniversalP2 : Polynomial K4FreeRing :=
  k4UniversalP1^2 + Polynomial.C (k4UniversalP1.eval (k4UniversalX 1)) * k4UniversalP1

def k4UniversalP3 : Polynomial K4FreeRing :=
  k4UniversalP2^2 + Polynomial.C (k4UniversalP2.eval (k4UniversalX 2)) * k4UniversalP2

def k4UniversalP4 : Polynomial K4FreeRing :=
  k4UniversalP3^2 + Polynomial.C (k4UniversalP3.eval (k4UniversalX 3)) * k4UniversalP3

lemma coeff_zero_sq_of_coeff_zero {R : Type*} [Semiring R]
    (p : Polynomial R) (hp : p.coeff 0 = 0) : (p^2).coeff 0 = 0 := by
  rw [pow_two, Polynomial.coeff_mul]
  simp [hp]

lemma coeff_two_sq_char_two (p : Polynomial K4FreeRing) (h0 : p.coeff 0 = 0) :
    (p^2).coeff 2 = p.coeff 1 ^ 2 := by
  rw [pow_two, Polynomial.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ, h0]
  ring

lemma coeff_one_sq_char_two (p : Polynomial K4FreeRing) (h0 : p.coeff 0 = 0) :
    (p^2).coeff 1 = 0 := by
  rw [pow_two, Polynomial.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ, h0]

lemma coeff_zero_P1 : k4UniversalP1.coeff 0 = 0 := by simp [k4UniversalP1]
lemma coeff_zero_P2 : k4UniversalP2.coeff 0 = 0 := by
  rw [k4UniversalP2, Polynomial.coeff_add, coeff_zero_sq_of_coeff_zero _ coeff_zero_P1]
  simp [coeff_zero_P1]
lemma coeff_zero_P3 : k4UniversalP3.coeff 0 = 0 := by
  rw [k4UniversalP3, Polynomial.coeff_add, coeff_zero_sq_of_coeff_zero _ coeff_zero_P2]
  simp [coeff_zero_P2]
lemma coeff_one_P1 : k4UniversalP1.coeff 1 = k4UniversalX 0 := by simp [k4UniversalP1]
lemma coeff_two_P1 : k4UniversalP1.coeff 2 = 1 := by simp [k4UniversalP1]
lemma coeff_one_P2 : k4UniversalP2.coeff 1 =
    k4UniversalP1.eval (k4UniversalX 1) * k4UniversalX 0 := by
  rw [k4UniversalP2, Polynomial.coeff_add, coeff_one_sq_char_two _ coeff_zero_P1]
  simp only [Polynomial.coeff_C_mul]
  rw [coeff_one_P1]
  simp
lemma coeff_two_P2 : k4UniversalP2.coeff 2 =
    k4UniversalX 0^2 + k4UniversalP1.eval (k4UniversalX 1) := by
  rw [k4UniversalP2, Polynomial.coeff_add, coeff_two_sq_char_two _ coeff_zero_P1]
  simp only [Polynomial.coeff_C_mul]
  rw [coeff_one_P1, coeff_two_P1]
  simp
lemma coeff_one_P3 : k4UniversalP3.coeff 1 =
    k4UniversalP2.eval (k4UniversalX 2) *
      (k4UniversalP1.eval (k4UniversalX 1) * k4UniversalX 0) := by
  rw [k4UniversalP3, Polynomial.coeff_add, coeff_one_sq_char_two _ coeff_zero_P2]
  simp only [Polynomial.coeff_C_mul]
  rw [coeff_one_P2]
  simp
lemma coeff_two_P3 : k4UniversalP3.coeff 2 =
    (k4UniversalP1.eval (k4UniversalX 1) * k4UniversalX 0)^2 +
      k4UniversalP2.eval (k4UniversalX 2) *
        (k4UniversalX 0^2 + k4UniversalP1.eval (k4UniversalX 1)) := by
  rw [k4UniversalP3, Polynomial.coeff_add, coeff_two_sq_char_two _ coeff_zero_P2]
  simp only [Polynomial.coeff_C_mul]
  rw [coeff_one_P2, coeff_two_P2]

#print axioms coeff_zero_sq_of_coeff_zero
#print axioms coeff_zero_P2
#print axioms coeff_one_P2
#print axioms coeff_two_P2
#print axioms coeff_one_P3
#print axioms coeff_two_P3
end Carlet
