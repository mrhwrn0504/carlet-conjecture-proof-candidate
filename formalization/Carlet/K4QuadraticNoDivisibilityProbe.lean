import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable (K : Type*) [Field K] [CharP K 2]

abbrev K4SymmetricRing := MvPolynomial (Fin 4) K

def k4e1 : K4SymmetricRing K :=
  MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3

def k4e2 : K4SymmetricRing K :=
  MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
  MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2 +
  MvPolynomial.X 1 * MvPolynomial.X 3 + MvPolynomial.X 2 * MvPolynomial.X 3

def k4e3 : K4SymmetricRing K :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
  MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
  MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3

def k4A : K4SymmetricRing K := k4e1 K * (k4e1 K * k4e2 K + k4e3 K)
def k4B : K4SymmetricRing K := k4e1 K ^ 4 + k4e2 K ^ 2 + k4e1 K * k4e3 K

private def k4TestPoint : Fin 4 → K := fun i =>
  if i = 0 ∨ i = 1 then 1 else 0

lemma k4e1_eval_testPoint : MvPolynomial.eval (k4TestPoint K) (k4e1 K) = 0 := by
  simp [k4e1, k4TestPoint]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination h2

omit [CharP K 2] in
lemma k4e2_eval_testPoint : MvPolynomial.eval (k4TestPoint K) (k4e2 K) = 1 := by
  simp [k4e2, k4TestPoint]

omit [CharP K 2] in
lemma k4e3_eval_testPoint : MvPolynomial.eval (k4TestPoint K) (k4e3 K) = 0 := by
  simp [k4e3, k4TestPoint]

lemma k4A_eval_testPoint : MvPolynomial.eval (k4TestPoint K) (k4A K) = 0 := by
  simp [k4A, k4e1_eval_testPoint, k4e2_eval_testPoint,
    k4e3_eval_testPoint]

lemma k4B_eval_testPoint : MvPolynomial.eval (k4TestPoint K) (k4B K) = 1 := by
  simp [k4B, k4e1_eval_testPoint, k4e2_eval_testPoint,
    k4e3_eval_testPoint]

theorem k4A_not_dvd_k4B : ¬ k4A K ∣ k4B K := by
  rintro ⟨q, hq⟩
  have he := congrArg (MvPolynomial.eval (k4TestPoint K)) hq
  rw [MvPolynomial.eval_mul, k4A_eval_testPoint, k4B_eval_testPoint] at he
  norm_num at he

#print axioms k4A_not_dvd_k4B
end Carlet
