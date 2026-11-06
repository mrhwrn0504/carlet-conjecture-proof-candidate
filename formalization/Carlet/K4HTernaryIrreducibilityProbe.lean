import Carlet.K4HQuarticIrreducibleProbe
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

abbrev HCoeff (K : Type*) [Field K] := MvPolynomial (Fin 2) K

def k4HP : HCoeff K := MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1

def k4HTernaryAsQuartic : Polynomial (HCoeff K) :=
  X^4 + C (k4HP K)*X^2 + C (MvPolynomial.X 0 * MvPolynomial.X 1 *
    (MvPolynomial.X 0 + MvPolynomial.X 1))*X + C ((k4HP K)^2)

def k4HDehomCoeff : HCoeff K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![1, Polynomial.X]

omit [Algebra (ZMod 2) K] in
theorem k4HTernaryAsQuartic_monic : (k4HTernaryAsQuartic K).Monic := by
  unfold k4HTernaryAsQuartic
  monicity <;> norm_num

omit [Algebra (ZMod 2) K] in
theorem k4HTernaryAsQuartic_map :
    (k4HTernaryAsQuartic K).map (k4HDehomCoeff K) = k4HQuartic K := by
  simp [k4HTernaryAsQuartic, k4HDehomCoeff, k4HP, k4HQuartic, k4QP,
    MvPolynomial.eval₂Hom]
  ring

theorem k4HTernaryAsQuartic_irreducible : Irreducible (k4HTernaryAsQuartic K) := by
  apply Polynomial.Monic.irreducible_of_irreducible_map (k4HDehomCoeff K)
    (k4HTernaryAsQuartic K) (k4HTernaryAsQuartic_monic K)
  rw [k4HTernaryAsQuartic_map]
  exact k4HQuartic_irreducible K

#print axioms k4HTernaryAsQuartic_irreducible
end Carlet
