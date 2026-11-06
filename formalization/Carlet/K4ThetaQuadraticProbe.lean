import Carlet.K4ThetaSymmetricIdentityProbe
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

noncomputable section
namespace Carlet
open Polynomial

local instance : CharP K4FreeRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* K4FreeRing)
    exact MvPolynomial.C_injective _ _) 2

def theta4SymmetricA : K4FreeRing :=
  theta4Elementary1 * (theta4Elementary1 * theta4Elementary2 + theta4Elementary3)

def theta4SymmetricB : K4FreeRing :=
  theta4Elementary1 ^ 4 + theta4Elementary2 ^ 2 +
    theta4Elementary1 * theta4Elementary3

def theta4AsPolynomial : Polynomial K4FreeRing :=
  X ^ 2 + C theta4SymmetricA * X + C (theta4SymmetricB ^ 2)

theorem theta4_as_polynomial_eval :
    theta4AsPolynomial.eval theta4Elementary4 = theta4 := by
  rw [theta4_elementary_symmetric_identity]
  simp [theta4AsPolynomial, theta4SymmetricA, theta4SymmetricB]

theorem theta4AsPolynomial_derivative :
    derivative theta4AsPolynomial = C theta4SymmetricA := by
  have h2 : (2 : K4FreeRing) = 0 := CharP.cast_eq_zero K4FreeRing 2
  simp [theta4AsPolynomial, derivative_add, derivative_mul,
    derivative_pow, derivative_C, derivative_X, h2]

#print axioms theta4_as_polynomial_eval
#print axioms theta4AsPolynomial_derivative
end Carlet
