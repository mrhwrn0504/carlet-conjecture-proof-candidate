import Carlet.K4ThetaFactorCoefficientProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet

theorem unit_of_irreducible_product_not_dvd {R : Type*} [CommRing R] [IsDomain R]
    (h u v : R) (hi : Irreducible h) (hp : Prime h)
    (hprod : h^2 = u*v) (hn : ¬ (h ∣ u ∧ h ∣ v)) : IsUnit u ∨ IsUnit v := by
  have hd : h ∣ u*v := by
    refine ⟨h, ?_⟩
    simpa [pow_two] using hprod.symm
  rcases hp.dvd_mul.mp hd with hu | hv
  · have hnv : ¬h ∣ v := by intro hv; exact hn ⟨hu,hv⟩
    obtain ⟨a, ha⟩ := hu
    have hc : h = a*v := by
      apply mul_left_cancel₀ hi.ne_zero
      calc
        h*h = u*v := by simpa [pow_two] using hprod
        _ = (h*a)*v := by rw [ha]
        _ = h*(a*v) := by ring
    rcases hi.isUnit_or_isUnit hc with haunit | hvunit
    · exfalso
      apply hnv
      obtain ⟨ai, hai⟩ := (isUnit_iff_exists_inv).mp haunit
      refine ⟨ai, ?_⟩
      calc
        v = v*1 := by simp
        _ = v*(a*ai) := by rw [hai]
        _ = (a*v)*ai := by ring
        _ = h*ai := by rw [hc]
    · exact Or.inr hvunit
  · have hnu : ¬h ∣ u := by intro hu; exact hn ⟨hu,hv⟩
    obtain ⟨a, ha⟩ := hv
    have hc : h = u*a := by
      apply mul_left_cancel₀ hi.ne_zero
      calc
        h*h = u*v := by simpa [pow_two] using hprod
        _ = u*(h*a) := by rw [ha]
        _ = h*(u*a) := by ring
    rcases hi.isUnit_or_isUnit hc with huunit | haunit
    · exact Or.inl huunit
    · exfalso
      apply hnu
      obtain ⟨ai, hai⟩ := (isUnit_iff_exists_inv).mp haunit
      refine ⟨ai, ?_⟩
      calc
        u = u*1 := by simp
        _ = u*(a*ai) := by rw [hai]
        _ = (u*a)*ai := by ring
        _ = h*ai := by rw [hc]

variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
def k4ThetaPolyOver : Polynomial (MvPolynomial (Fin 3) K) :=
  (theta4PolynomialEquiv theta4).map (MvPolynomial.map (algebraMap (ZMod 2) K))

theorem k4ThetaPolyOver_coeff_zero : (k4ThetaPolyOver K).coeff 0 = (k4HOver K)^2 := by
  simp only [k4ThetaPolyOver, Polynomial.coeff_map]
  exact k4Theta_constant_coefficient_over K

theorem k4ThetaPolyOver_coeff_one : ¬ k4HOver K ∣ (k4ThetaPolyOver K).coeff 1 := by
  simp only [k4ThetaPolyOver, Polynomial.coeff_map]
  exact k4H_not_dvd_theta4_linear_coefficient K

theorem k4Theta_factors_constant_unit (f g : Polynomial (MvPolynomial (Fin 3) K))
    (hf : k4ThetaPolyOver K = f*g) : IsUnit (f.coeff 0) ∨ IsUnit (g.coeff 0) := by
  have hprod : (k4HOver K)^2 = f.coeff 0 * g.coeff 0 := by
    have hc := congrArg (fun p : Polynomial (MvPolynomial (Fin 3) K) => p.coeff 0) hf
    rw [k4ThetaPolyOver_coeff_zero] at hc
    simpa using hc
  have hn : ¬ (k4HOver K ∣ f.coeff 0 ∧ k4HOver K ∣ g.coeff 0) := by
    apply factor_constants_cannot_both_be_divisible
    rw [← hf]
    exact k4ThetaPolyOver_coeff_one K
  exact unit_of_irreducible_product_not_dvd _ _ _ (k4HOver_irreducible K)
    ((irreducible_iff_prime).mp (k4HOver_irreducible K)) hprod hn

#print axioms unit_of_irreducible_product_not_dvd
#print axioms k4Theta_factors_constant_unit
end Carlet
