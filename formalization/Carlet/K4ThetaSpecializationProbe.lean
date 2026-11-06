import Carlet.K4ThetaIdentityProbe

noncomputable section
set_option maxRecDepth 10000
namespace Carlet

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

def k4SpecialHom (x : Fin 4 → K) : K4FreeRing →+* K :=
  MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K) x

def k4SpecialP1 (x : Fin 4 → K) : Polynomial K :=
  k4UniversalP1.map (k4SpecialHom x)

def k4SpecialP2 (x : Fin 4 → K) : Polynomial K :=
  k4UniversalP2.map (k4SpecialHom x)

def k4SpecialP3 (x : Fin 4 → K) : Polynomial K :=
  k4UniversalP3.map (k4SpecialHom x)

def k4SpecialPolynomial (x : Fin 4 → K) : Polynomial K :=
  k4UniversalP4.map (k4SpecialHom x)

lemma k4_map_eval (x : Fin 4 → K) (p : Polynomial K4FreeRing) (a : K4FreeRing) :
    k4SpecialHom x (p.eval a) = (p.map (k4SpecialHom x)).eval (k4SpecialHom x a) := by
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map]

lemma k4SpecialHom_X (x : Fin 4 → K) (i : Fin 4) :
    k4SpecialHom x (k4UniversalX i) = x i := by
  simp [k4SpecialHom, k4UniversalX]

theorem k4SpecialP1_eq (x : Fin 4 → K) :
    k4SpecialP1 x = Polynomial.X ^ 2 + Polynomial.C (x 0) * Polynomial.X := by
  simp [k4SpecialP1, k4UniversalP1, k4SpecialHom_X]

theorem k4SpecialP2_eq (x : Fin 4 → K) :
    k4SpecialP2 x = k4SpecialP1 x ^ 2 +
      Polynomial.C ((k4SpecialP1 x).eval (x 1)) * k4SpecialP1 x := by
  simp only [k4SpecialP2, k4UniversalP2, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, k4_map_eval,
    k4SpecialHom_X, k4SpecialP1]

theorem k4SpecialP3_eq (x : Fin 4 → K) :
    k4SpecialP3 x = k4SpecialP2 x ^ 2 +
      Polynomial.C ((k4SpecialP2 x).eval (x 2)) * k4SpecialP2 x := by
  simp only [k4SpecialP3, k4UniversalP3, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, k4_map_eval,
    k4SpecialHom_X, k4SpecialP2]

theorem k4SpecialPolynomial_eq (x : Fin 4 → K) :
    k4SpecialPolynomial x = k4SpecialP3 x ^ 2 +
      Polynomial.C ((k4SpecialP3 x).eval (x 3)) * k4SpecialP3 x := by
  simp only [k4SpecialPolynomial, k4UniversalP4, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, k4_map_eval,
    k4SpecialHom_X, k4SpecialP3]

theorem k4SpecialPolynomial_coeff_eight (x : Fin 4 → K) :
    (k4SpecialPolynomial x).coeff 8 =
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) := by
  rw [k4SpecialPolynomial, Polynomial.coeff_map,
    k4UniversalP4_coeff_eight_eq_theta4, MvPolynomial.eval_map]
  rfl

#print axioms k4SpecialP1_eq
#print axioms k4SpecialP2_eq
#print axioms k4SpecialP3_eq
#print axioms k4SpecialPolynomial_eq
#print axioms k4SpecialPolynomial_coeff_eight
end Carlet
