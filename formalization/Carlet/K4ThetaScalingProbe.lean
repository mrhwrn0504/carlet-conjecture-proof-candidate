import Carlet.K4ScalingMapProbe
import Carlet.K4ThetaProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

def k4ThetaOver : MvPolynomial (Fin 4) K := theta4.map (algebraMap (ZMod 2) K)

theorem k4ThetaOver_scaling : k4Scale (k4ThetaOver K) = C (k4ThetaOver K) * X^8 := by
  simp [k4Scale, k4ThetaOver, theta4, k4X, MvPolynomial.eval₂Hom]
  ring

#print axioms k4ThetaOver_scaling
end Carlet
