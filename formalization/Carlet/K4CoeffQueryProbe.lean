import Carlet.K4CoordCoverageProbe
import Mathlib.Tactic
open Polynomial
namespace Carlet
example {R : Type*} [Semiring R] (p q : Polynomial R) :
    (p*q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  simp
example {R : Type*} [Semiring R] (p q : Polynomial R) :
    (p*q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  simp [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
end Carlet
