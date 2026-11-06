import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000

namespace Carlet

private abbrev K4Index := Fin 4

def k4X (i : K4Index) : MvPolynomial K4Index (ZMod 2) :=
  MvPolynomial.X i

/-- The explicit symmetric degree-eight polynomial Θ₄ from the standard
    finite-field criterion. The five summands are the monomial-symmetric
    terms of exponent patterns (8), (4,4), (4,2,2), (4,2,1,1), (2,2,2,2). -/
def theta4 : MvPolynomial K4Index (ZMod 2) :=
    k4X 0 ^ 8
  + k4X 1 ^ 8
  + k4X 2 ^ 8
  + k4X 3 ^ 8
  + k4X 0 ^ 4 * k4X 1 ^ 4
  + k4X 0 ^ 4 * k4X 2 ^ 4
  + k4X 0 ^ 4 * k4X 3 ^ 4
  + k4X 1 ^ 4 * k4X 2 ^ 4
  + k4X 1 ^ 4 * k4X 3 ^ 4
  + k4X 2 ^ 4 * k4X 3 ^ 4
  + k4X 1 ^ 4 * k4X 2 ^ 2 * k4X 3 ^ 2
  + k4X 1 ^ 2 * k4X 2 ^ 4 * k4X 3 ^ 2
  + k4X 1 ^ 2 * k4X 2 ^ 2 * k4X 3 ^ 4
  + k4X 0 ^ 4 * k4X 2 ^ 2 * k4X 3 ^ 2
  + k4X 0 ^ 2 * k4X 2 ^ 4 * k4X 3 ^ 2
  + k4X 0 ^ 2 * k4X 2 ^ 2 * k4X 3 ^ 4
  + k4X 0 ^ 4 * k4X 1 ^ 2 * k4X 3 ^ 2
  + k4X 0 ^ 2 * k4X 1 ^ 4 * k4X 3 ^ 2
  + k4X 0 ^ 2 * k4X 1 ^ 2 * k4X 3 ^ 4
  + k4X 0 ^ 4 * k4X 1 ^ 2 * k4X 2 ^ 2
  + k4X 0 ^ 2 * k4X 1 ^ 4 * k4X 2 ^ 2
  + k4X 0 ^ 2 * k4X 1 ^ 2 * k4X 2 ^ 4
  + k4X 0 ^ 4 * k4X 1 ^ 2 * k4X 2 * k4X 3
  + k4X 0 ^ 4 * k4X 2 ^ 2 * k4X 1 * k4X 3
  + k4X 0 ^ 4 * k4X 3 ^ 2 * k4X 1 * k4X 2
  + k4X 1 ^ 4 * k4X 0 ^ 2 * k4X 2 * k4X 3
  + k4X 1 ^ 4 * k4X 2 ^ 2 * k4X 0 * k4X 3
  + k4X 1 ^ 4 * k4X 3 ^ 2 * k4X 0 * k4X 2
  + k4X 2 ^ 4 * k4X 0 ^ 2 * k4X 1 * k4X 3
  + k4X 2 ^ 4 * k4X 1 ^ 2 * k4X 0 * k4X 3
  + k4X 2 ^ 4 * k4X 3 ^ 2 * k4X 0 * k4X 1
  + k4X 3 ^ 4 * k4X 0 ^ 2 * k4X 1 * k4X 2
  + k4X 3 ^ 4 * k4X 1 ^ 2 * k4X 0 * k4X 2
  + k4X 3 ^ 4 * k4X 2 ^ 2 * k4X 0 * k4X 1
  + k4X 0 ^ 2 * k4X 1 ^ 2 * k4X 2 ^ 2 * k4X 3 ^ 2

/-- At (1,0,0,0), only the `(8)` term survives. This certifies that the
    explicit Θ₄ polynomial is nonzero in the project representation. -/
theorem theta4_eval_first_unit :
    MvPolynomial.eval (fun i : K4Index => if i = 0 then (1 : ZMod 2) else 0) theta4 = 1 := by
  classical
  norm_num [theta4, k4X]; decide

theorem theta4_ne_zero : theta4 ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval
    (fun i : K4Index => if i = 0 then (1 : ZMod 2) else 0)) h
  rw [theta4_eval_first_unit] at he
  simp at he


#print axioms theta4_eval_first_unit
#print axioms theta4_ne_zero
end Carlet
