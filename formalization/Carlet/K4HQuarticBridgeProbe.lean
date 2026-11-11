import Carlet.K4SpecializationHProbe
import Carlet.K4HQuadraticExtractionProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def k4HToQuartic : Hring →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
    ((Polynomial.C : K →+* Polynomial K).comp (algebraMap (ZMod 2) K)))
    ![Polynomial.C (Polynomial.X : Polynomial K), 1, Polynomial.X]

theorem k4HToQuartic_eq : k4HToQuartic K k4H = k4HQuartic K := by
  simp [k4HToQuartic, k4H, k4HQuartic, k4QP, MvPolynomial.eval₂Hom]
  have h2 : (2 : Polynomial (Polynomial K)) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : Polynomial (Polynomial K)) = 1 := by linear_combination h2
  ring_nf
  simp [h2, h3]

#print axioms k4HToQuartic_eq
end Carlet
