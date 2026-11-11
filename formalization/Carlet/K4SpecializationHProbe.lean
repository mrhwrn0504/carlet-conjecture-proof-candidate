import Carlet.K4ThetaSymmetricIdentityProbe
import Mathlib.Tactic

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Carlet

abbrev Hring := MvPolynomial (Fin 3) (ZMod 2)
def k4H : Hring :=
  let x : Hring := MvPolynomial.X 0
  let y : Hring := MvPolynomial.X 1
  let z : Hring := MvPolynomial.X 2
  x^4 + y^4 + z^4 + x^2*y^2 + x^2*z^2 + y^2*z^2 + x*y*z*(x+y+z)

def theta4AtZero : Hring :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ZMod 2 →+* Hring)
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] theta4

theorem theta4_at_zero_eq_H_squared : theta4AtZero = k4H^2 := by
  unfold theta4AtZero k4H theta4 k4X
  simp only [map_add, map_mul, map_pow]
  simp only [MvPolynomial.eval₂Hom]
  have h2 : (2 : Hring) = 0 := by
    have : CharP Hring 2 := charP_of_injective_algebraMap (by
      change Function.Injective (MvPolynomial.C : ZMod 2 →+* Hring)
      exact MvPolynomial.C_injective _ _) 2
    exact CharP.cast_eq_zero Hring 2
  have h3 : (3 : Hring) = 1 := by linear_combination h2
  have h4 : (4 : Hring) = 0 := by linear_combination (2 : Hring) * h2
  have h5 : (5 : Hring) = 1 := by linear_combination (2 : Hring) * h2
  ring_nf
  simp [h2, h3, h4, h5]

#print axioms theta4_at_zero_eq_H_squared
end Carlet

