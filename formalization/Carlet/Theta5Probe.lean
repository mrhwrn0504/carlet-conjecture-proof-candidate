import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Carlet

abbrev Theta5Index := Fin 5
def theta5X (i : Theta5Index) : MvPolynomial Theta5Index (ZMod 2) :=
  MvPolynomial.X i

/-- Monomial-symmetric Θ₅ component for exponent partition (16,). -/
def theta5Part0 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 4 ^ 16 +
  theta5X 3 ^ 16 +
  theta5X 2 ^ 16 +
  theta5X 1 ^ 16 +
  theta5X 0 ^ 16

/-- Monomial-symmetric Θ₅ component for exponent partition (8, 8). -/
def theta5Part1 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 3 ^ 8 * theta5X 4 ^ 8 +
  theta5X 2 ^ 8 * theta5X 4 ^ 8 +
  theta5X 2 ^ 8 * theta5X 3 ^ 8 +
  theta5X 1 ^ 8 * theta5X 4 ^ 8 +
  theta5X 1 ^ 8 * theta5X 3 ^ 8 +
  theta5X 1 ^ 8 * theta5X 2 ^ 8 +
  theta5X 0 ^ 8 * theta5X 4 ^ 8 +
  theta5X 0 ^ 8 * theta5X 3 ^ 8 +
  theta5X 0 ^ 8 * theta5X 2 ^ 8 +
  theta5X 0 ^ 8 * theta5X 1 ^ 8

/-- Monomial-symmetric Θ₅ component for exponent partition (8, 4, 4). -/
def theta5Part2 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 2 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 2 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 2 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 1 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 1 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 4 ^ 8 +
  theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 8 +
  theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 4 ^ 4 +
  theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 4 +
  theta5X 1 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 4 ^ 4 +
  theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 4 +
  theta5X 0 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 2 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 8 +
  theta5X 0 ^ 4 * theta5X 2 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 3 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 2 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 3 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 2 ^ 4 +
  theta5X 0 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 2 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 3 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 2 ^ 4

/-- Monomial-symmetric Θ₅ component for exponent partition (8, 4, 2, 2). -/
def theta5Part3 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 2 +
  theta5X 0 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 2 +
  theta5X 0 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 2

/-- Monomial-symmetric Θ₅ component for exponent partition (8, 4, 2, 1, 1). -/
def theta5Part4 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 0 ^ 1 * theta5X 1 ^ 1 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 1 * theta5X 1 ^ 1 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 1 * theta5X 1 ^ 1 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 1 * theta5X 1 ^ 1 * theta5X 2 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 1 * theta5X 1 ^ 1 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 1 * theta5X 1 ^ 1 * theta5X 2 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 1 * theta5X 1 ^ 2 * theta5X 2 ^ 1 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 1 * theta5X 1 ^ 2 * theta5X 2 ^ 1 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 1 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 1 * theta5X 4 ^ 8 +
  theta5X 0 ^ 1 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 1 +
  theta5X 0 ^ 1 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 1 * theta5X 4 ^ 4 +
  theta5X 0 ^ 1 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 1 +
  theta5X 0 ^ 1 * theta5X 1 ^ 4 * theta5X 2 ^ 1 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 1 * theta5X 1 ^ 4 * theta5X 2 ^ 1 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 1 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 1 * theta5X 4 ^ 8 +
  theta5X 0 ^ 1 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 1 +
  theta5X 0 ^ 1 * theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 1 * theta5X 4 ^ 2 +
  theta5X 0 ^ 1 * theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 1 +
  theta5X 0 ^ 1 * theta5X 1 ^ 8 * theta5X 2 ^ 1 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 1 * theta5X 1 ^ 8 * theta5X 2 ^ 1 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 1 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 1 * theta5X 4 ^ 4 +
  theta5X 0 ^ 1 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 1 +
  theta5X 0 ^ 1 * theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 1 * theta5X 4 ^ 2 +
  theta5X 0 ^ 1 * theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 1 +
  theta5X 0 ^ 2 * theta5X 1 ^ 1 * theta5X 2 ^ 1 * theta5X 3 ^ 4 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 1 * theta5X 2 ^ 1 * theta5X 3 ^ 8 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 1 * theta5X 2 ^ 4 * theta5X 3 ^ 1 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 1 * theta5X 2 ^ 4 * theta5X 3 ^ 8 * theta5X 4 ^ 1 +
  theta5X 0 ^ 2 * theta5X 1 ^ 1 * theta5X 2 ^ 8 * theta5X 3 ^ 1 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 1 * theta5X 2 ^ 8 * theta5X 3 ^ 4 * theta5X 4 ^ 1 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 1 * theta5X 3 ^ 1 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 1 * theta5X 3 ^ 8 * theta5X 4 ^ 1 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 8 * theta5X 3 ^ 1 * theta5X 4 ^ 1 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 1 * theta5X 3 ^ 1 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 1 * theta5X 3 ^ 4 * theta5X 4 ^ 1 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 4 * theta5X 3 ^ 1 * theta5X 4 ^ 1 +
  theta5X 0 ^ 4 * theta5X 1 ^ 1 * theta5X 2 ^ 1 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 1 * theta5X 2 ^ 1 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 1 * theta5X 2 ^ 2 * theta5X 3 ^ 1 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 1 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 1 +
  theta5X 0 ^ 4 * theta5X 1 ^ 1 * theta5X 2 ^ 8 * theta5X 3 ^ 1 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 1 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 1 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 1 * theta5X 3 ^ 1 * theta5X 4 ^ 8 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 1 * theta5X 3 ^ 8 * theta5X 4 ^ 1 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 1 * theta5X 4 ^ 1 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 2 ^ 1 * theta5X 3 ^ 1 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 2 ^ 1 * theta5X 3 ^ 2 * theta5X 4 ^ 1 +
  theta5X 0 ^ 4 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 1 * theta5X 4 ^ 1 +
  theta5X 0 ^ 8 * theta5X 1 ^ 1 * theta5X 2 ^ 1 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 1 * theta5X 2 ^ 1 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 1 * theta5X 2 ^ 2 * theta5X 3 ^ 1 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 1 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 1 +
  theta5X 0 ^ 8 * theta5X 1 ^ 1 * theta5X 2 ^ 4 * theta5X 3 ^ 1 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 1 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 1 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 1 * theta5X 3 ^ 1 * theta5X 4 ^ 4 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 1 * theta5X 3 ^ 4 * theta5X 4 ^ 1 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 1 * theta5X 4 ^ 1 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 2 ^ 1 * theta5X 3 ^ 1 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 2 ^ 1 * theta5X 3 ^ 2 * theta5X 4 ^ 1 +
  theta5X 0 ^ 8 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 1 * theta5X 4 ^ 1

/-- Monomial-symmetric Θ₅ component for exponent partition (8, 2, 2, 2, 2). -/
def theta5Part5 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 8 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 8 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 8 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 2 * theta5X 1 ^ 8 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 2 +
  theta5X 0 ^ 8 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 2

/-- Monomial-symmetric Θ₅ component for exponent partition (4, 4, 4, 4). -/
def theta5Part6 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 4

/-- Monomial-symmetric Θ₅ component for exponent partition (4, 4, 4, 2, 2). -/
def theta5Part7 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5X 0 ^ 2 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 2 * theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 2 * theta5X 2 ^ 4 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 2 * theta5X 4 ^ 4 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 2 ^ 2 * theta5X 3 ^ 4 * theta5X 4 ^ 2 +
  theta5X 0 ^ 4 * theta5X 1 ^ 4 * theta5X 2 ^ 4 * theta5X 3 ^ 2 * theta5X 4 ^ 2

/-- The 185-term symmetric polynomial Θ₅ from the finite-field criterion. -/
def theta5 : MvPolynomial Theta5Index (ZMod 2) :=
  theta5Part0 + theta5Part1 + theta5Part2 + theta5Part3 +
    theta5Part4 + theta5Part5 + theta5Part6 + theta5Part7

theorem theta5Part0_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part0 = 1 := by
  simp [theta5Part0, theta5X]

theorem theta5Part1_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part1 = 0 := by
  simp [theta5Part1, theta5X]

theorem theta5Part2_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part2 = 0 := by
  simp [theta5Part2, theta5X]

theorem theta5Part3_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part3 = 0 := by
  simp [theta5Part3, theta5X]

theorem theta5Part4_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part4 = 0 := by
  simp [theta5Part4, theta5X]

theorem theta5Part5_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part5 = 0 := by
  simp [theta5Part5, theta5X]

theorem theta5Part6_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part6 = 0 := by
  simp [theta5Part6, theta5X]

theorem theta5Part7_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5Part7 = 0 := by
  simp [theta5Part7, theta5X]

theorem theta5Part0_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part0 = 0 := by
  simp [theta5Part0, theta5X]; decide

theorem theta5Part1_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part1 = 1 := by
  simp [theta5Part1, theta5X]

theorem theta5Part2_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part2 = 0 := by
  simp [theta5Part2, theta5X]

theorem theta5Part3_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part3 = 0 := by
  simp [theta5Part3, theta5X]

theorem theta5Part4_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part4 = 0 := by
  simp [theta5Part4, theta5X]

theorem theta5Part5_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part5 = 0 := by
  simp [theta5Part5, theta5X]

theorem theta5Part6_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part6 = 0 := by
  simp [theta5Part6, theta5X]

theorem theta5Part7_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5Part7 = 0 := by
  simp [theta5Part7, theta5X]


/-- At one coordinate equal to 1, only the `(16)` term survives. -/
theorem theta5_eval_first_unit :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0) theta5 = 1 := by
  simp only [theta5, MvPolynomial.eval_add, theta5Part0_eval_first_unit,
    theta5Part1_eval_first_unit, theta5Part2_eval_first_unit,
    theta5Part3_eval_first_unit, theta5Part4_eval_first_unit,
    theta5Part5_eval_first_unit, theta5Part6_eval_first_unit,
    theta5Part7_eval_first_unit]
  norm_num

/-- At `(1,1,0,0,0)`, the `(8,8)` term survives in characteristic two. -/
theorem theta5_eval_two_units :
    MvPolynomial.eval (fun i : Theta5Index => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta5 = 1 := by
  simp only [theta5, MvPolynomial.eval_add, theta5Part0_eval_two_units,
    theta5Part1_eval_two_units, theta5Part2_eval_two_units,
    theta5Part3_eval_two_units, theta5Part4_eval_two_units,
    theta5Part5_eval_two_units, theta5Part6_eval_two_units,
    theta5Part7_eval_two_units]
  norm_num

theorem theta5_ne_zero : theta5 ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval
    (fun i : Theta5Index => if i = 0 then (1 : ZMod 2) else 0)) h
  rw [theta5_eval_first_unit] at he
  simp at he

#print axioms theta5_eval_first_unit
#print axioms theta5_eval_two_units
#print axioms theta5_ne_zero
end Carlet
