import Carlet.K4CoeffRecursionProbe
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.NormNum

noncomputable section
open Polynomial MvPolynomial
namespace Carlet

set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : CharP K4FreeRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* K4FreeRing)
    exact MvPolynomial.C_injective _ _) 2

lemma coeff_square_free (p : Polynomial K4FreeRing) (i : ℕ) :
    (p^2).coeff i = if 2 ∣ i then (p.coeff (i/2))^2 else 0 := by
  rw [← map_frobenius_expand 2 p, Polynomial.coeff_map,
    Polynomial.coeff_expand (by decide)]
  split_ifs <;> simp [frobenius_def]

lemma coeff_four_P1 : k4UniversalP1.coeff 4 = 0 := by simp [k4UniversalP1]
lemma coeff_eight_P1 : k4UniversalP1.coeff 8 = 0 := by simp [k4UniversalP1]

lemma coeff_four_P2 : k4UniversalP2.coeff 4 = 1 := by
  rw [k4UniversalP2, Polynomial.coeff_add, coeff_square_free]
  norm_num [Polynomial.coeff_C_mul, coeff_two_P1, coeff_four_P1]

lemma coeff_eight_P2 : k4UniversalP2.coeff 8 = 0 := by
  rw [k4UniversalP2, Polynomial.coeff_add, coeff_square_free]
  norm_num [Polynomial.coeff_C_mul, coeff_four_P1, coeff_eight_P1]

lemma coeff_four_P3 : k4UniversalP3.coeff 4 =
    k4UniversalP2.coeff 2 ^ 2 + k4UniversalP2.eval (k4UniversalX 2) := by
  rw [k4UniversalP3, Polynomial.coeff_add, coeff_square_free]
  norm_num [Polynomial.coeff_C_mul, coeff_four_P2]

lemma coeff_eight_P3 : k4UniversalP3.coeff 8 = 1 := by
  rw [k4UniversalP3, Polynomial.coeff_add, coeff_square_free]
  norm_num [Polynomial.coeff_C_mul, coeff_four_P2, coeff_eight_P2]

lemma coeff_eight_P4 : k4UniversalP4.coeff 8 =
    k4UniversalP3.coeff 4 ^ 2 + k4UniversalP3.eval (k4UniversalX 3) := by
  rw [k4UniversalP4, Polynomial.coeff_add, coeff_square_free]
  norm_num [Polynomial.coeff_C_mul, coeff_eight_P3]


#print axioms coeff_square_free
#print axioms coeff_four_P3
#print axioms coeff_eight_P4
end Carlet
