import Carlet.Theta5Probe
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

noncomputable section
open Polynomial MvPolynomial
namespace Carlet

abbrev T5EvalIndex := Fin 5
abbrev T5EvalRing := MvPolynomial T5EvalIndex (ZMod 2)

local instance t5EvalRingCharTwo : CharP T5EvalRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* T5EvalRing)
    exact MvPolynomial.C_injective _ _) 2

def t5EvalX (i : T5EvalIndex) : T5EvalRing := MvPolynomial.X i

def t5EvalP1 : Polynomial T5EvalRing :=
  Polynomial.X ^ 2 + Polynomial.C (t5EvalX 0) * Polynomial.X

def t5EvalP2 : Polynomial T5EvalRing :=
  t5EvalP1 ^ 2 + Polynomial.C (t5EvalP1.eval (t5EvalX 1)) * t5EvalP1

def t5EvalP3 : Polynomial T5EvalRing :=
  t5EvalP2 ^ 2 + Polynomial.C (t5EvalP2.eval (t5EvalX 2)) * t5EvalP2

def t5EvalP4 : Polynomial T5EvalRing :=
  t5EvalP3 ^ 2 + Polynomial.C (t5EvalP3.eval (t5EvalX 3)) * t5EvalP3

/-- Evaluation is reduced one extension at a time. Keeping these intermediate
    identities avoids expanding all five basis variables inside one ring proof. -/
lemma t5EvalP1_at (a : T5EvalRing) :
    t5EvalP1.eval a = a ^ 2 + t5EvalX 0 * a := by
  simp [t5EvalP1, t5EvalX]

lemma t5EvalP2_at (a : T5EvalRing) :
    t5EvalP2.eval a =
      (t5EvalP1.eval a) ^ 2 +
        (t5EvalP1.eval (t5EvalX 1)) * (t5EvalP1.eval a) := by
  simp [t5EvalP2, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]

lemma t5EvalP3_at (a : T5EvalRing) :
    t5EvalP3.eval a =
      (t5EvalP2.eval a) ^ 2 +
        (t5EvalP2.eval (t5EvalX 2)) * (t5EvalP2.eval a) := by
  simp [t5EvalP3, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]

lemma t5EvalP4_at (a : T5EvalRing) :
    t5EvalP4.eval a =
      (t5EvalP3.eval a) ^ 2 +
        (t5EvalP3.eval (t5EvalX 3)) * (t5EvalP3.eval a) := by
  simp [t5EvalP4, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]

/-- A coefficient-free expression for evaluation after each extension step.
    These aliases let later proofs normalize one degree at a time. -/
def t5EvalValue1 (a : T5EvalRing) : T5EvalRing :=
  a ^ 2 + t5EvalX 0 * a

def t5EvalValue2 (a : T5EvalRing) : T5EvalRing :=
  t5EvalValue1 a ^ 2 + t5EvalValue1 (t5EvalX 1) * t5EvalValue1 a

def t5EvalValue3 (a : T5EvalRing) : T5EvalRing :=
  t5EvalValue2 a ^ 2 + t5EvalValue2 (t5EvalX 2) * t5EvalValue2 a

def t5EvalValue4 (a : T5EvalRing) : T5EvalRing :=
  t5EvalValue3 a ^ 2 + t5EvalValue3 (t5EvalX 3) * t5EvalValue3 a

lemma t5EvalP1_value (a : T5EvalRing) :
    t5EvalP1.eval a = t5EvalValue1 a := by
  exact t5EvalP1_at a

lemma t5EvalP2_value (a : T5EvalRing) :
    t5EvalP2.eval a = t5EvalValue2 a := by
  rw [t5EvalP2_at, t5EvalP1_value, t5EvalP1_value]
  rfl

lemma t5EvalP3_value (a : T5EvalRing) :
    t5EvalP3.eval a = t5EvalValue3 a := by
  rw [t5EvalP3_at, t5EvalP2_value, t5EvalP2_value]
  rfl

lemma t5EvalP4_value (a : T5EvalRing) :
    t5EvalP4.eval a = t5EvalValue4 a := by
  rw [t5EvalP4_at, t5EvalP3_value, t5EvalP3_value]
  rfl

#print axioms t5EvalP1_at
#print axioms t5EvalP2_at
#print axioms t5EvalP3_at
#print axioms t5EvalP4_at
#print axioms t5EvalP2_value
#print axioms t5EvalP3_value
#print axioms t5EvalP4_value

end Carlet
