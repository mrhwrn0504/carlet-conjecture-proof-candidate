import Carlet.K4HTernaryIrreducibilityProbe
import Carlet.K4HLinearFactorBridgeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def k4HPolynomialEquiv : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (HCoeff K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 3) 2)).trans
    (MvPolynomial.finSuccEquiv K 2)

theorem k4HPolynomialEquiv_apply :
    k4HPolynomialEquiv K (k4HOver K) = k4HTernaryAsQuartic K := by
  have hX1 : (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X (1 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := (0 : Fin 2)))
  have hX2 : (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X (2 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 2)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := (1 : Fin 2)))
  simp [k4HPolynomialEquiv, k4HOver, k4H, k4HTernaryAsQuartic, k4HP,
    MvPolynomial.renameEquiv, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_zero,
    Equiv.swap_apply_def, hX1, hX2]
  have h2 : (2 : Polynomial (HCoeff K)) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : Polynomial (HCoeff K)) = 1 := by linear_combination h2
  ring_nf
  simp [h2, h3]

theorem k4HOver_irreducible : Irreducible (k4HOver K) := by
  have hback : (k4HPolynomialEquiv K).symm (k4HTernaryAsQuartic K) = k4HOver K := by
    have h := congrArg (k4HPolynomialEquiv K).symm (k4HPolynomialEquiv_apply K)
    simpa using h.symm
  rw [← hback]
  exact Irreducible.map (k4HPolynomialEquiv K).symm (k4HTernaryAsQuartic_irreducible K)

#print axioms k4HPolynomialEquiv_apply
#print axioms k4HOver_irreducible
end Carlet
