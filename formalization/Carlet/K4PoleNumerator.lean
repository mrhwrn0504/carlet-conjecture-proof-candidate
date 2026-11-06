import Carlet.K4PoleData
open Polynomial
noncomputable section
namespace Carlet

def k4PoleNumOneF2 : Polynomial (ZMod 2) := X^4+X^2
def k4PoleNum02F2 : Polynomial (ZMod 2) := X^6+1

def k4PoleNumOnePoly (K : Type*) [Field K] : Polynomial K := X^4+X^2
def k4PoleNum02Poly (K : Type*) [Field K] : Polynomial K := X^6+1

lemma k4_pole_num_one_bezout_f2 : (1 : Polynomial (ZMod 2)) =
    (X^2+X+1)*k4PoleDenF2 + (X^4+X+1)*k4PoleNumOneF2 := by
  unfold k4PoleDenF2 k4PoleNumOneF2
  ring_nf
  ext n
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one, h2, h4]

lemma k4_pole_num02_bezout_f2 : (1 : Polynomial (ZMod 2)) =
    (X^5+X^4+X^3+X^2+X)*k4PoleDenF2 +
      (X^5+X^3+X+1)*k4PoleNum02F2 := by
  unfold k4PoleDenF2 k4PoleNum02F2
  ring_nf
  ext n
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h6 : (6 : ZMod 2) = 0 := by decide
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one, h2, h4, h6]

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

lemma k4_pole_num_one_bezout : (1 : Polynomial K) =
    (X^2+X+1)*k4PoleDenPoly K + (X^4+X+1)*k4PoleNumOnePoly K := by
  have hmap := congrArg (Polynomial.map (algebraMap (ZMod 2) K)) k4_pole_num_one_bezout_f2
  simpa [k4PoleDenF2, k4PoleNumOneF2, k4PoleDenPoly, k4PoleNumOnePoly] using hmap

lemma k4_pole_num02_bezout : (1 : Polynomial K) =
    (X^5+X^4+X^3+X^2+X)*k4PoleDenPoly K +
      (X^5+X^3+X+1)*k4PoleNum02Poly K := by
  have hmap := congrArg (Polynomial.map (algebraMap (ZMod 2) K)) k4_pole_num02_bezout_f2
  simpa [k4PoleDenF2, k4PoleNum02F2, k4PoleDenPoly, k4PoleNum02Poly] using hmap

lemma k4_pole_den_num_one_coprime :
    IsCoprime (k4PoleDenPoly K) (k4PoleNumOnePoly K) := by
  exact ⟨X^2+X+1, X^4+X+1,
    by simpa using k4_pole_num_one_bezout.symm⟩

lemma k4_pole_den_num02_coprime :
    IsCoprime (k4PoleDenPoly K) (k4PoleNum02Poly K) := by
  exact ⟨X^5+X^4+X^3+X^2+X, X^5+X^3+X+1,
    by simpa using k4_pole_num02_bezout.symm⟩

lemma k4_pole_num_one_eval (t : K) :
    Polynomial.eval t (k4PoleNumOnePoly K) = (t^2+t)^2 := by
  simp only [k4PoleNumOnePoly, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hcross : t^2*t + t^2*t = 0 := CharTwo.add_self_eq_zero _
  calc
    t^4+t^2 = t^4 + (t^2*t+t^2*t) + t^2 := by rw [hcross]; ring
    _ = (t^2+t)^2 := by ring

omit [Algebra (ZMod 2) K] in
lemma k4_pole_num02_eval (t : K) :
    Polynomial.eval t (k4PoleNum02Poly K) = t^6+1 := by
  simp [k4PoleNum02Poly]

#print axioms k4_pole_num_one_bezout_f2
#print axioms k4_pole_num02_bezout_f2
#print axioms k4_pole_num_one_bezout
#print axioms k4_pole_num02_bezout
#print axioms k4_pole_den_num_one_coprime
#print axioms k4_pole_den_num02_coprime
#print axioms k4_pole_num_one_eval
#print axioms k4_pole_num02_eval
end Carlet
