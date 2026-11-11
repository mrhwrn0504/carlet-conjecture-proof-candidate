import Mathlib
import Carlet.Statement
open Polynomial
noncomputable section
namespace Carlet

def k4PoleDenF2 : Polynomial (ZMod 2) := X^6+X^5+X^4+X^3+X^2+X+1
def k4PoleDerivF2 : Polynomial (ZMod 2) := X^4+X^2+1

def k4PoleDenPoly (K : Type*) [Field K] : Polynomial K :=
  X^6+X^5+X^4+X^3+X^2+X+1
def k4PoleDerivPoly (K : Type*) [Field K] : Polynomial K :=
  X^4+X^2+1

def k4PoleDenominator {K : Type*} [Field K] (t : K) : K :=
  (t^2+t)^3+(t^2+t)+1

lemma k4_pole_deriv_f2 : Polynomial.derivative k4PoleDenF2 = k4PoleDerivF2 := by
  unfold k4PoleDenF2 k4PoleDerivF2
  simp
  ring_nf
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;> simp [Polynomial.coeff_X_pow,
      Polynomial.coeff_X] <;> decide
  · have hn' : 6 < n := by omega
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X,
      show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega]
    omega

lemma k4_pole_den_bezout_f2 : (1 : Polynomial (ZMod 2)) =
    k4PoleDenF2 + (X^2+X)*k4PoleDerivF2 := by
  unfold k4PoleDenF2 k4PoleDerivF2
  ring_nf
  ext n
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one, h2]

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

lemma k4_pole_deriv :
    Polynomial.derivative (k4PoleDenPoly K) = k4PoleDerivPoly K := by
  have hm : Polynomial.map (algebraMap (ZMod 2) K) k4PoleDenF2 = k4PoleDenPoly K := by
    simp [k4PoleDenF2, k4PoleDenPoly]
  rw [← hm, Polynomial.derivative_map]
  have h := congrArg (Polynomial.map (algebraMap (ZMod 2) K)) k4_pole_deriv_f2
  simpa [k4PoleDerivF2, k4PoleDerivPoly] using h

lemma k4_pole_den_bezout : (1 : Polynomial K) =
    k4PoleDenPoly K + (X^2+X)*k4PoleDerivPoly K := by
  have hmap := congrArg (Polynomial.map (algebraMap (ZMod 2) K)) k4_pole_den_bezout_f2
  simpa [k4PoleDenF2, k4PoleDerivF2, k4PoleDenPoly, k4PoleDerivPoly] using hmap

lemma k4_pole_den_coprime_derivative :
    IsCoprime (k4PoleDenPoly K) (Polynomial.derivative (k4PoleDenPoly K)) := by
  rw [k4_pole_deriv]
  exact ⟨1, X^2+X, by simpa [one_mul] using k4_pole_den_bezout.symm⟩

lemma k4_pole_den_eval_eq (t : K) : k4PoleDenominator t =
    Polynomial.eval t (k4PoleDenPoly K) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [k4PoleDenominator, k4PoleDenPoly, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
  linear_combination (t^4 + t^5) * h2

#print axioms k4_pole_deriv_f2
#print axioms k4_pole_den_bezout_f2
#print axioms k4_pole_deriv
#print axioms k4_pole_den_bezout
#print axioms k4_pole_den_coprime_derivative
#print axioms k4_pole_den_eval_eq
end Carlet

