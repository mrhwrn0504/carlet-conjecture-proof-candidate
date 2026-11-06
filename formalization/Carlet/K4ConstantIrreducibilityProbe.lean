import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable (K : Type*) [Field K] [CharP K 2]

abbrev K4SymmetricPolyRing := MvPolynomial (Fin 3) K
abbrev K4CoeffPolyRing := MvPolynomial (Fin 2) K

def k4ConstantB : K4SymmetricPolyRing K :=
  MvPolynomial.X 0 ^ 4 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 2

def k4ConstantA : K4SymmetricPolyRing K :=
  MvPolynomial.X 0 * (MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 2)

def k4BReindexEquiv : K4SymmetricPolyRing K ≃ₐ[K] K4SymmetricPolyRing K :=
  MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 3) 2)

def k4BPolynomialEquiv : K4SymmetricPolyRing K ≃ₐ[K] Polynomial (K4CoeffPolyRing K) :=
  (k4BReindexEquiv K).trans (MvPolynomial.finSuccEquiv K 2)

def k4LinearCoeffA : K4CoeffPolyRing K := MvPolynomial.X 1
def k4LinearCoeffB : K4CoeffPolyRing K :=
  MvPolynomial.X 1 ^ 4 + MvPolynomial.X 0 ^ 2

def k4BAsLinearPolynomial : Polynomial (K4CoeffPolyRing K) :=
  Polynomial.C (k4LinearCoeffA K) * Polynomial.X + Polynomial.C (k4LinearCoeffB K)

omit [CharP K 2] in
lemma k4BPolynomialEquiv_apply :
    k4BPolynomialEquiv K (k4ConstantB K) = k4BAsLinearPolynomial K := by
  have hX1 : (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X (1 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2)
      (j := (0 : Fin 2)))
  have hX2 : (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X (2 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 2)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2)
      (j := (1 : Fin 2)))
  simp [k4BPolynomialEquiv, k4BReindexEquiv, k4ConstantB,
    k4BAsLinearPolynomial, k4LinearCoeffA, k4LinearCoeffB,
    MvPolynomial.renameEquiv, MvPolynomial.rename_X,
    MvPolynomial.finSuccEquiv_X_zero, Equiv.swap_apply_def, hX1, hX2]
  ring

private def k4CoeffTestPoint : Fin 2 → K := fun i => if i = 0 then 1 else 0

omit [CharP K 2] in
lemma k4LinearCoeffA_irreducible : Irreducible (k4LinearCoeffA K) := by
  let e : K4CoeffPolyRing K ≃ₐ[K] Polynomial (MvPolynomial (Fin 1) K) :=
    (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)).trans
      (MvPolynomial.finSuccEquiv K 1)
  have he : e (k4LinearCoeffA K) = Polynomial.X := by
    simp [e, k4LinearCoeffA, MvPolynomial.renameEquiv, MvPolynomial.rename_X,
      MvPolynomial.finSuccEquiv_X_zero]
  have hirr : Irreducible (Polynomial.X : Polynomial (MvPolynomial (Fin 1) K)) :=
    Polynomial.irreducible_X
  have h := Irreducible.map e.symm hirr
  have heback : e.symm Polynomial.X = k4LinearCoeffA K := by
    rw [← he]
    exact e.symm_apply_apply _
  simpa [heback] using h

omit [CharP K 2] in
lemma k4LinearCoeffA_not_dvd_B : ¬ k4LinearCoeffA K ∣ k4LinearCoeffB K := by
  rintro ⟨q, hq⟩
  have he := congrArg (MvPolynomial.eval (k4CoeffTestPoint K)) hq
  simp [k4LinearCoeffA, k4LinearCoeffB, k4CoeffTestPoint] at he

omit [CharP K 2] in
lemma k4LinearCoeffA_relPrime_B :
    IsRelPrime (k4LinearCoeffA K) (k4LinearCoeffB K) :=
  (Irreducible.isRelPrime_iff_not_dvd (k4LinearCoeffA_irreducible K)).2
    (k4LinearCoeffA_not_dvd_B K)

omit [CharP K 2] in
theorem k4ConstantB_irreducible : Irreducible (k4ConstantB K) := by
  have hlin : Irreducible (k4BAsLinearPolynomial K) :=
    Polynomial.irreducible_C_mul_X_add_C
      (k4LinearCoeffA_irreducible K).ne_zero (k4LinearCoeffA_relPrime_B K)
  have hback : (k4BPolynomialEquiv K).symm (k4BAsLinearPolynomial K) =
      k4ConstantB K := by
    have h := congrArg (k4BPolynomialEquiv K).symm (k4BPolynomialEquiv_apply K)
    simpa using h.symm
  rw [← hback]
  exact Irreducible.map (k4BPolynomialEquiv K).symm hlin

private def k4ConstantDivisibilityTestPoint : Fin 3 → K := fun i =>
  if i = 0 then 1 else if i = 1 then 0 else 1

theorem k4ConstantB_not_dvd_A : ¬ k4ConstantB K ∣ k4ConstantA K := by
  rintro ⟨q, hq⟩
  have heval := congrArg (MvPolynomial.eval (k4ConstantDivisibilityTestPoint K)) hq
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [k4ConstantDivisibilityTestPoint, k4ConstantB, k4ConstantA] at heval
  rw [show (1 : K) + 1 = 2 by norm_num, htwo, zero_mul] at heval
  norm_num at heval

omit [CharP K 2] in
theorem k4_irreducible_square_factor_cases (u v : K4SymmetricPolyRing K)
    (huv : (k4ConstantB K) ^ 2 = u * v) :
    IsUnit u ∨ (k4ConstantB K ∣ u ∧ k4ConstantB K ∣ v) ∨
      (k4ConstantB K) ^ 2 ∣ u := by
  let b := k4ConstantB K
  have hbIrr : Irreducible b := by simpa [b] using k4ConstantB_irreducible K
  have hbPrime : Prime b := (irreducible_iff_prime).mp hbIrr
  have hb0 : b ≠ 0 := hbIrr.ne_zero
  have hbDiv : b ∣ u * v := by
    refine ⟨b, ?_⟩
    simpa [pow_two] using huv.symm
  rcases hbPrime.dvd_mul.mp hbDiv with hbu | hbv
  · rcases hbu with ⟨a, ha⟩
    have hcancel : b = a * v := by
      apply mul_left_cancel₀ hb0
      calc
        b * b = u * v := by simpa [pow_two] using huv
        _ = (b * a) * v := by rw [ha]
        _ = b * (a * v) := by ac_rfl
    rcases hbIrr.isUnit_or_isUnit hcancel with haUnit | hvUnit
    · right
      left
      constructor
      · exact ⟨a, ha⟩
      · let ai : K4SymmetricPolyRing K := ↑(haUnit.unit⁻¹)
        have hai : ai * a = 1 := by
          calc
            ai * a = (↑(haUnit.unit⁻¹) : K4SymmetricPolyRing K) * ↑haUnit.unit := by
              dsimp [ai]
            _ = 1 := Units.inv_mul _
        have hai' : a * ai = 1 := by simpa [mul_comm] using hai
        refine ⟨ai, ?_⟩
        calc
          v = v * 1 := by simp
          _ = v * (a * ai) := by rw [hai']
          _ = (a * v) * ai := by ac_rfl
          _ = b * ai := by rw [← hcancel]
    · right
      right
      let vi : K4SymmetricPolyRing K := ↑(hvUnit.unit⁻¹)
      have hvi : vi * v = 1 := by
        calc
          vi * v = (↑(hvUnit.unit⁻¹) : K4SymmetricPolyRing K) * ↑hvUnit.unit := by
            dsimp [vi]
          _ = 1 := Units.inv_mul _
      have hvi' : v * vi = 1 := by simpa [mul_comm] using hvi
      have haeq : a = b * vi := by
        calc
          a = a * 1 := by simp
          _ = a * (v * vi) := by rw [hvi']
          _ = (a * v) * vi := by ac_rfl
          _ = b * vi := by rw [hcancel]
      refine ⟨vi, ?_⟩
      rw [ha]
      rw [haeq]
      ring
  · rcases hbv with ⟨a, ha⟩
    have hcancel : b = u * a := by
      apply mul_left_cancel₀ hb0
      calc
        b * b = u * v := by simpa [pow_two] using huv
        _ = u * (b * a) := by rw [ha]
        _ = b * (u * a) := by ac_rfl
    rcases hbIrr.isUnit_or_isUnit hcancel with huUnit | haUnit
    · exact Or.inl huUnit
    · right
      left
      constructor
      · let ai : K4SymmetricPolyRing K := ↑(haUnit.unit⁻¹)
        have hai : ai * a = 1 := by
          calc
            ai * a = (↑(haUnit.unit⁻¹) : K4SymmetricPolyRing K) * ↑haUnit.unit := by
              dsimp [ai]
            _ = 1 := Units.inv_mul _
        have hai' : a * ai = 1 := by simpa [mul_comm] using hai
        have hueq : u = b * ai := by
          calc
            u = u * 1 := by simp
            _ = u * (a * ai) := by rw [hai']
            _ = (u * a) * ai := by ac_rfl
            _ = b * ai := by rw [hcancel]
        exact ⟨ai, hueq⟩
      · exact ⟨a, ha⟩

#print axioms k4ConstantB_irreducible
#print axioms k4ConstantB_not_dvd_A
#print axioms k4_irreducible_square_factor_cases
end Carlet
