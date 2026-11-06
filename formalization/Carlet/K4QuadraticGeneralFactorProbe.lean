import Carlet.K4QuadraticNormalFormProbe
import Carlet.K4QuadraticCoeffThreeProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem k4H_quadratic_equations_general_impossible (A B D : Polynomial K)
    (hs : B+D = k4QP K + A^2)
    (ha : A*(B+D) = X*(X+1)) (hp : B*D = (k4QP K)^2) : False := by
  have hA : A.natDegree ≤ 1 := by
    apply k4Quadratic_A_degree_le_one K A
    simpa [hs] using ha
  have hB : B.natDegree ≤ 2 := k4Quadratic_B_degree_le_two K A B D hA hs hp
  have h2 : (2 : Polynomial K) = 0 := CharP.cast_eq_zero _ 2
  have hD : D = B + k4QP K + A^2 := by
    linear_combination hs - B*h2
  have hA' : A*(k4QP K + A^2) = X*(X+1) := by simpa [hs] using ha
  have hB' : B*(B+k4QP K+A^2) = (k4QP K)^2 := by simpa [hD] using hp
  rw [k4Polynomial_normal_linear K A hA] at hA' hB'
  rw [k4Polynomial_normal_quadratic K B hB] at hB'
  exact k4H_quadratic_equations_impossible K (A.coeff 1) (A.coeff 0)
    (B.coeff 2) (B.coeff 1) (B.coeff 0) hA' hB'

#print axioms k4H_quadratic_equations_general_impossible
end Carlet
