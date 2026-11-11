import Carlet.K4CoeffRecursionProbe
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Carlet
local instance : CharP K4FreeRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* K4FreeRing)
    exact MvPolynomial.C_injective _ _) 2
private def theta4Vars : Fin 4 → K4FreeRing := MvPolynomial.X
def theta4Elementary1 : K4FreeRing := theta4Vars 0 + theta4Vars 1 + theta4Vars 2 + theta4Vars 3
def theta4Elementary2 : K4FreeRing := theta4Vars 0 * theta4Vars 1 + theta4Vars 0 * theta4Vars 2 + theta4Vars 0 * theta4Vars 3 + theta4Vars 1 * theta4Vars 2 + theta4Vars 1 * theta4Vars 3 + theta4Vars 2 * theta4Vars 3
def theta4Elementary3 : K4FreeRing := theta4Vars 0 * theta4Vars 1 * theta4Vars 2 + theta4Vars 0 * theta4Vars 1 * theta4Vars 3 + theta4Vars 0 * theta4Vars 2 * theta4Vars 3 + theta4Vars 1 * theta4Vars 2 * theta4Vars 3
def theta4Elementary4 : K4FreeRing := theta4Vars 0 * theta4Vars 1 * theta4Vars 2 * theta4Vars 3
theorem theta4_elementary_symmetric_identity :
    theta4 = theta4Elementary4 ^ 2 + theta4Elementary1 * (theta4Elementary1 * theta4Elementary2 + theta4Elementary3) * theta4Elementary4 + (theta4Elementary1 ^ 4 + theta4Elementary2 ^ 2 + theta4Elementary1 * theta4Elementary3) ^ 2 := by
  simp only [theta4, k4X, theta4Elementary1, theta4Elementary2, theta4Elementary3, theta4Elementary4, theta4Vars]
  have h2 : (2 : K4FreeRing) = 0 := CharP.cast_eq_zero K4FreeRing 2
  linear_combination ((-4 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 7) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 6) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-41 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) ^ 6 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (2 : Fin 4)) ^ 7 * (MvPolynomial.X (3 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 7) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 6) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 6 * (MvPolynomial.X (3 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 7) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 6) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4))) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 6) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4))) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 5) +
      (-41 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4))) +
      (-41 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 4) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 3) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 7 * (MvPolynomial.X (3 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (1 : Fin 4)) ^ 7 * (MvPolynomial.X (2 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 7) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 6) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 6 * (MvPolynomial.X (3 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 7) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 6) +
      (-214 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-841 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-214 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4))) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 6) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4))) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 5) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-841 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-841 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4))) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 4) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 3) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-214 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (3 : Fin 4))) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) * (MvPolynomial.X (1 : Fin 4)) ^ 7) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 6) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4))) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 6) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4))) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 5) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-2083 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4))) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 4) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 3) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4))) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4))) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 6) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 5) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4))) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 5) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-841 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-841 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4))) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 4) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-1321 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 3) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-841 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-402 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4))) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4))) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 3 * (MvPolynomial.X (1 : Fin 4)) ^ 5) +
      (-41 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (3 : Fin 4)) ^ 4) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4))) +
      (-41 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (2 : Fin 4)) ^ 4) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 3) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-601 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-288 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (3 : Fin 4))) +
      (-185 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 3 * (MvPolynomial.X (2 : Fin 4))) +
      (-41 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 4 * (MvPolynomial.X (1 : Fin 4)) ^ 4) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (3 : Fin 4)) ^ 3) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (2 : Fin 4)) ^ 3) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-214 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4))) +
      (-103 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4))) +
      (-32 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 5 * (MvPolynomial.X (1 : Fin 4)) ^ 3) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (3 : Fin 4)) ^ 2) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (2 : Fin 4)) ^ 2) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (3 : Fin 4))) +
      (-31 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (1 : Fin 4)) * (MvPolynomial.X (2 : Fin 4))) +
      (-15 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 6 * (MvPolynomial.X (1 : Fin 4)) ^ 2) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 7 * (MvPolynomial.X (3 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 7 * (MvPolynomial.X (2 : Fin 4))) +
      (-4 : K4FreeRing) * ((MvPolynomial.X (0 : Fin 4)) ^ 7 * (MvPolynomial.X (1 : Fin 4)))) * h2
#print axioms theta4_elementary_symmetric_identity
end Carlet
