import Carlet.N9FieldBridgeProbe
import Carlet.N9K5InverseAdjoinProbe
import Carlet.K4BadLocusSZProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial MvPolynomial Carlet
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩

def thetaBadX0 : P17 := Polynomial.X^7 + Polynomial.X^6 + Polynomial.X^4 + Polynomial.X^3 + 1
def thetaBadX1 : P17 := Polynomial.X^7 + Polynomial.X^6 + Polynomial.X^3 + Polynomial.X^2
def thetaBadX2 : P17 := Polynomial.X^6 + 1
def thetaBadX3 : P17 := Polynomial.X^7 + Polynomial.X^5

def thetaBadI1 : P17 := Polynomial.X^6 + Polynomial.X^5 + Polynomial.X^4 +
  Polynomial.X^3 + Polynomial.X^2 + Polynomial.X + 1
def thetaBadQ1 : P17 := Polynomial.X^4 + Polynomial.X

theorem thetaBadInv1_poly : thetaBadX0 * thetaBadI1 + 1 = f9 * thetaBadQ1 := by
  norm_num [thetaBadX0, thetaBadI1, thetaBadQ1, f9]
  ring_nf
  have h2 : (2 : P17) = 0 := CharP.cast_eq_zero P17 2
  have h3 : (3 : P17) = 1 := by
    calc
      (3 : P17) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have h4 : (4 : P17) = 0 := by
    calc
      (4 : P17) = 2 * 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  simp [h2, h3, h4]

theorem thetaBadInv1_field :
    (AdjoinRoot.mk f9 thetaBadX0) * (AdjoinRoot.mk f9 thetaBadI1) = 1 :=
  n9K5InvAdjoin_of_poly thetaBadInv1_poly

#print axioms thetaBadInv1_poly
#print axioms thetaBadInv1_field
