import Carlet.K4HAbsoluteIrreducibleProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

def k4HAxis0 : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![X,0,0]
def k4HAxis1 : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![0,X,0]
def k4HAxis2 : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![0,0,X]

theorem k4H_not_dvd_if_axis (l : MvPolynomial (Fin 3) K)
    (e : MvPolynomial (Fin 3) K →+* Polynomial K)
    (hl : e l = X) (hh : e (k4HOver K) = X^4) : ¬ k4HOver K ∣ l := by
  intro hd
  have he := map_dvd e hd
  rw [hh, hl] at he
  have hdeg := Polynomial.natDegree_le_of_dvd he (Polynomial.X_ne_zero : (X : Polynomial K) ≠ 0)
  simp at hdeg

theorem k4H_not_dvd_x0 : ¬ k4HOver K ∣ MvPolynomial.X 0 := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis0 K) <;> simp [k4HAxis0, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_x1 : ¬ k4HOver K ∣ MvPolynomial.X 1 := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis1 K) <;> simp [k4HAxis1, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_x2 : ¬ k4HOver K ∣ MvPolynomial.X 2 := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis2 K) <;> simp [k4HAxis2, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_x01 : ¬ k4HOver K ∣ (MvPolynomial.X 0 + MvPolynomial.X 1) := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis0 K) <;> simp [k4HAxis0, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_x02 : ¬ k4HOver K ∣ (MvPolynomial.X 0 + MvPolynomial.X 2) := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis0 K) <;> simp [k4HAxis0, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_x12 : ¬ k4HOver K ∣ (MvPolynomial.X 1 + MvPolynomial.X 2) := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis1 K) <;> simp [k4HAxis1, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_x012 : ¬ k4HOver K ∣ (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2) := by
  apply k4H_not_dvd_if_axis K _ (k4HAxis0 K) <;> simp [k4HAxis0, k4HOver, k4H, MvPolynomial.eval₂Hom]

theorem k4H_not_dvd_linear_coefficient : ¬ k4HOver K ∣
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 *
      (MvPolynomial.X 0+MvPolynomial.X 1) * (MvPolynomial.X 0+MvPolynomial.X 2) *
      (MvPolynomial.X 1+MvPolynomial.X 2) *
      (MvPolynomial.X 0+MvPolynomial.X 1+MvPolynomial.X 2)) := by
  intro hd
  have hp : Prime (k4HOver K) := (irreducible_iff_prime).mp (k4HOver_irreducible K)
  repeat' first | rcases hp.dvd_mul.mp hd with hd | hd
  all_goals first
    | exact k4H_not_dvd_x0 K hd
    | exact k4H_not_dvd_x1 K hd
    | exact k4H_not_dvd_x2 K hd
    | exact k4H_not_dvd_x01 K hd
    | exact k4H_not_dvd_x02 K hd
    | exact k4H_not_dvd_x12 K hd
    | exact k4H_not_dvd_x012 K hd

#print axioms k4H_not_dvd_linear_coefficient
end Carlet
