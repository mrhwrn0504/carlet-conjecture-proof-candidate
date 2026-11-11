import Carlet.K4SymmetricSubalgebraProbe
import Carlet.K4ThetaSymmetricIdentityProbe
import Mathlib.Tactic

noncomputable section
set_option maxRecDepth 10000
namespace Carlet

theorem k4_esymm_one : MvPolynomial.esymm (Fin 4) (ZMod 2) 1 = theta4Elementary1 := by
  change MvPolynomial.esymm (Fin 4) (ZMod 2) 1 =
    MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3
  rw [MvPolynomial.esymm_one]
  simp [Fin.sum_univ_succ, add_assoc]

theorem k4_esymm_two : MvPolynomial.esymm (Fin 4) (ZMod 2) 2 = theta4Elementary2 := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {({0,1} : Finset (Fin 4)), {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} := by decide
  change MvPolynomial.esymm (Fin 4) (ZMod 2) 2 =
    MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 1 * MvPolynomial.X 3 + MvPolynomial.X 2 * MvPolynomial.X 3
  rw [MvPolynomial.esymm, hs]
  simp (disch := decide) [Finset.sum_insert, Finset.prod_insert]
  ring

theorem k4_esymm_three : MvPolynomial.esymm (Fin 4) (ZMod 2) 3 = theta4Elementary3 := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 3 =
      {({0,1,2} : Finset (Fin 4)), {0,1,3}, {0,2,3}, {1,2,3}} := by decide
  change MvPolynomial.esymm (Fin 4) (ZMod 2) 3 =
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
    MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3
  rw [MvPolynomial.esymm, hs]
  simp (disch := decide) [Finset.sum_insert, Finset.prod_insert]
  ring

theorem k4_esymm_four : MvPolynomial.esymm (Fin 4) (ZMod 2) 4 = theta4Elementary4 := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 4 =
      {({0,1,2,3} : Finset (Fin 4))} := by decide
  change MvPolynomial.esymm (Fin 4) (ZMod 2) 4 =
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3
  rw [MvPolynomial.esymm, hs]
  simp [Finset.prod_insert, mul_assoc]

theorem k4ThetaSymmetricElement_coe_eq_theta4 :
    (k4ThetaSymmetricElement (ZMod 2) : MvPolynomial (Fin 4) (ZMod 2)) = theta4 := by
  rw [k4ThetaSymmetricElement_coe, k4_esymm_one, k4_esymm_two, k4_esymm_three,
    k4_esymm_four, theta4_elementary_symmetric_identity]

theorem theta4_irreducible_in_symmetric_subalgebra :
    Irreducible (k4ThetaSymmetricElement (ZMod 2)) :=
  k4ThetaSymmetricElement_irreducible (ZMod 2)

section BaseChange
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem k4ThetaSymmetricElement_coe_eq_theta4_map :
    (k4ThetaSymmetricElement K : MvPolynomial (Fin 4) K) =
      theta4.map (algebraMap (ZMod 2) K) := by
  rw [← k4ThetaSymmetricElement_coe_eq_theta4,
    k4ThetaSymmetricElement_coe K, k4ThetaSymmetricElement_coe (ZMod 2)]
  simp [MvPolynomial.map_esymm]

theorem theta4_map_irreducible_in_symmetric_subalgebra :
    ∃ p : MvPolynomial.symmetricSubalgebra (Fin 4) K,
      (p : MvPolynomial (Fin 4) K) = theta4.map (algebraMap (ZMod 2) K) ∧
        Irreducible p :=
  ⟨k4ThetaSymmetricElement K, k4ThetaSymmetricElement_coe_eq_theta4_map K,
    k4ThetaSymmetricElement_irreducible K⟩

/-- A symmetric divisor of the original Θ₄ cannot have a nonunit cofactor. -/
theorem theta4_map_symmetric_factor_has_unit (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsSymmetric) (hfactor : theta4.map (algebraMap (ZMod 2) K) = q * r) :
    IsUnit q ∨ IsUnit r := by
  obtain ⟨p, hp, hpIrr⟩ := theta4_map_irreducible_in_symmetric_subalgebra K
  have hpFactor : (p : MvPolynomial (Fin 4) K) = q * r := hp.trans hfactor
  have hq0 : q ≠ 0 := by
    intro hz
    have hp0 : p = 0 := by
      apply Subtype.ext
      simpa [hz] using hpFactor
    exact hpIrr.ne_zero hp0
  have hrSym : r.IsSymmetric := by
    intro e
    have hpSym : (p : MvPolynomial (Fin 4) K).IsSymmetric := p.property
    have h := hpSym e
    rw [hpFactor, map_mul, hq e] at h
    exact mul_left_cancel₀ hq0 h
  let q' : MvPolynomial.symmetricSubalgebra (Fin 4) K := ⟨q, hq⟩
  let r' : MvPolynomial.symmetricSubalgebra (Fin 4) K := ⟨r, hrSym⟩
  have hpFactor' : p = q' * r' := by
    apply Subtype.ext
    exact hpFactor
  rcases hpIrr.isUnit_or_isUnit hpFactor' with hqUnit | hrUnit
  · left
    exact hqUnit.map (MvPolynomial.symmetricSubalgebra (Fin 4) K).subtype
  · right
    exact hrUnit.map (MvPolynomial.symmetricSubalgebra (Fin 4) K).subtype
end BaseChange

#print axioms k4ThetaSymmetricElement_coe_eq_theta4
#print axioms theta4_irreducible_in_symmetric_subalgebra
#print axioms theta4_map_irreducible_in_symmetric_subalgebra
#print axioms theta4_map_symmetric_factor_has_unit
end Carlet
