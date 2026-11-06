import Carlet.K4ConstantIrreducibilityProbe
import Carlet.K4MonicQuadraticNoRootProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet
open Polynomial

variable (K : Type*) [Field K] [CharP K 2]

abbrev K4ThetaCoeffRing := MvPolynomial (Fin 3) K

def k4ThetaQuadratic : Polynomial (K4ThetaCoeffRing K) :=
  Polynomial.X ^ 2 + Polynomial.C (k4ConstantA K) * Polynomial.X +
    Polynomial.C ((k4ConstantB K) ^ 2)

private def k4ThetaOrigin : Fin 3 → K := fun _ => 0

theorem k4ThetaQuadratic_no_root (u : K4ThetaCoeffRing K) :
    (k4ThetaQuadratic K).eval u ≠ 0 := by
  intro hroot
  have hroot' : u ^ 2 + k4ConstantA K * u + (k4ConstantB K) ^ 2 = 0 := by
    simpa [k4ThetaQuadratic, Polynomial.eval_add, Polynomial.eval_mul] using hroot
  have hb0 : k4ConstantB K ≠ 0 := (k4ConstantB_irreducible K).ne_zero
  have hprod : (k4ConstantB K) ^ 2 = u * (u + k4ConstantA K) := by
    have h2 : (2 : K4ThetaCoeffRing K) = 0 := CharP.cast_eq_zero _ 2
    let s := u ^ 2 + k4ConstantA K * u
    have hss : s + s = 0 := by linear_combination s * h2
    calc
      (k4ConstantB K) ^ 2 = (k4ConstantB K) ^ 2 + 0 := by simp
      _ = (k4ConstantB K) ^ 2 + (s + s) := by rw [hss]
      _ = (s + (k4ConstantB K) ^ 2) + s := by dsimp [s]; ring
      _ = 0 + s := by rw [hroot']
      _ = u * (u + k4ConstantA K) := by dsimp [s]; ring
  rcases k4_irreducible_square_factor_cases K u (u + k4ConstantA K) hprod with
      huUnit | ⟨hbu, hbv⟩ | hbsq
  · let ev : K4ThetaCoeffRing K →+* K := MvPolynomial.eval (k4ThetaOrigin K)
    have heval := congrArg ev hroot'
    have huEvalUnit : IsUnit (ev u) := huUnit.map ev
    simp [ev, k4ThetaOrigin, k4ConstantA, k4ConstantB] at heval
    exact huEvalUnit.ne_zero heval
  · have hsum : k4ConstantB K ∣ u + (u + k4ConstantA K) := dvd_add hbu hbv
    have h2 : (2 : K4ThetaCoeffRing K) = 0 := CharP.cast_eq_zero _ 2
    have huu : u + u = 0 := by linear_combination u * h2
    have heq : u + (u + k4ConstantA K) = k4ConstantA K := by
      calc
        u + (u + k4ConstantA K) = (u + u) + k4ConstantA K := by ac_rfl
        _ = 0 + k4ConstantA K := by rw [huu]
        _ = k4ConstantA K := by simp
    have hBA : k4ConstantB K ∣ k4ConstantA K := by
      rw [heq] at hsum
      exact hsum
    exact k4ConstantB_not_dvd_A K hBA
  · obtain ⟨c, hc⟩ := hbsq
    have hcancelEq : (k4ConstantB K) ^ 2 * 1 =
        (k4ConstantB K) ^ 2 * (c * ((k4ConstantB K) ^ 2 * c + k4ConstantA K)) := by
      calc
        (k4ConstantB K) ^ 2 * 1 = (k4ConstantB K) ^ 2 := by simp
        _ = u * (u + k4ConstantA K) := hprod
        _ = (k4ConstantB K) ^ 2 * (c * ((k4ConstantB K) ^ 2 * c + k4ConstantA K)) := by
          rw [hc]
          ring
    have hquot : 1 = c * ((k4ConstantB K) ^ 2 * c + k4ConstantA K) :=
      mul_left_cancel₀ (pow_ne_zero 2 hb0) hcancelEq
    let ev : K4ThetaCoeffRing K →+* K := MvPolynomial.eval (k4ThetaOrigin K)
    have heval := congrArg ev hquot
    simp [ev, k4ThetaOrigin, k4ConstantA, k4ConstantB] at heval

theorem k4ThetaQuadratic_irreducible : Irreducible (k4ThetaQuadratic K) := by
  have hlin : (Polynomial.C (k4ConstantA K) * Polynomial.X +
      Polynomial.C ((k4ConstantB K) ^ 2)).natDegree ≤ 1 := by
    calc
      _ ≤ max (Polynomial.C (k4ConstantA K) * Polynomial.X).natDegree
          (Polynomial.C ((k4ConstantB K) ^ 2)).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by
        have hcx : (Polynomial.C (k4ConstantA K) * Polynomial.X).natDegree ≤ 1 := by
          calc
            _ ≤ (Polynomial.C (k4ConstantA K)).natDegree + Polynomial.X.natDegree :=
              Polynomial.natDegree_mul_le
            _ = 1 := by simp
        simp only [Polynomial.natDegree_C]
        omega
  have hmid : (Polynomial.X ^ 2 +
      Polynomial.C (k4ConstantA K) * Polynomial.X).natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · have hcx : (Polynomial.C (k4ConstantA K) * Polynomial.X).natDegree ≤ 1 := by
        calc
          _ ≤ (Polynomial.C (k4ConstantA K)).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 1 := by simp
      simp only [Polynomial.natDegree_X_pow]
      omega
  have hdeg : (k4ThetaQuadratic K).natDegree = 2 := by
    unfold k4ThetaQuadratic
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact hmid
    · rw [hmid]
      simp
  have hconst : ((Polynomial.C (k4ConstantB K)) ^ 2).coeff 2 = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simp
  have hcoeff : (k4ThetaQuadratic K).coeff 2 = 1 := by
    simp [k4ThetaQuadratic, hconst]
  have hmonic : (k4ThetaQuadratic K).Monic := by
    change (k4ThetaQuadratic K).leadingCoeff = 1
    rw [← Polynomial.coeff_natDegree, hdeg]
    exact hcoeff
  exact monic_quadratic_irreducible_of_no_root
    (k4ThetaQuadratic K) hmonic hdeg (k4ThetaQuadratic_no_root K)

#print axioms k4ThetaQuadratic_no_root
#print axioms k4ThetaQuadratic_irreducible
end Carlet
