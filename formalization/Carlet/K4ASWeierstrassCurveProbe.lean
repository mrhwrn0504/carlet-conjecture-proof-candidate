import HasseWeil.HasseBound
import Carlet.K4ArtinSchreierWeierstrassProbe

set_option linter.style.haveILetI false

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [CharP K 2]

def k4ASWeierstrassCurve (A B : K) : WeierstrassCurve K :=
  ⟨1, A^2+B+1, B, A+(A^2+B), B*(A+(A^2+B))+A^2⟩

omit [CharP K 2] in
theorem k4ASWeierstrassCurve_equation (A B x y : K) :
    (k4ASWeierstrassCurve A B).toAffine.Equation x y ↔
      y^2+x*y+B*y = x^3+(A^2+B+1)*x^2+
        (A+(A^2+B))*x+B*(A+(A^2+B))+A^2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [k4ASWeierstrassCurve, WeierstrassCurve.toAffine]
  constructor <;> intro h <;> simpa [add_assoc] using h

theorem k4ASWeierstrassCurve_discriminant (A B : K) :
    (k4ASWeierstrassCurve A B).Δ = (A^2+A*B+B^2)^2 := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K)=1 := by
    calc
      (3 : K) = (2 : K)+1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have h4 : (4 : K)=0 := by
    calc
      (4 : K) = (2 : K)*(2 : K) := by norm_num
      _ = 0 := by rw [h2]; simp
  rw [WeierstrassCurve.Δ_of_char_two, WeierstrassCurve.b₈_of_char_two]
  simp [k4ASWeierstrassCurve]
  ring_nf
  simp [h2,h3,h4]

theorem k4ASWeierstrassCurve_isElliptic (A B : K)
    (hnorm : A^2+A*B+B^2 ≠ 0) :
    (k4ASWeierstrassCurve A B).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, k4ASWeierstrassCurve_discriminant]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hnorm)

#print axioms k4ASWeierstrassCurve_equation
#print axioms k4ASWeierstrassCurve_discriminant
#print axioms k4ASWeierstrassCurve_isElliptic

section Finite

variable [Fintype K]

def k4ASWeierstrassPairs (A B : K) :=
  {xy : K × K // xy.2^2+xy.1*xy.2+B*xy.2 =
    xy.1^3+(A^2+B+1)*xy.1^2+(A+(A^2+B))*xy.1+
      B*(A+(A^2+B))+A^2}

noncomputable def k4ASAffinePointToWeierstrassPair
    (A B x δ : K) (hx : x ≠ 0)
    (hcurve : k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x) :
    k4ASWeierstrassPairs A B := by
  refine ⟨(k4ASWeierstrassX A x δ,
    k4ASWeierstrassY A B x δ), ?_⟩
  have h := k4ASCurveWeierstrass_equation A B x δ hx hcurve
  simpa [k4ASC] using h

instance k4ASWeierstrassPairsFintype (A B : K) :
    Fintype (k4ASWeierstrassPairs A B) := by
  classical
  unfold k4ASWeierstrassPairs
  exact Fintype.ofFinite _

noncomputable def k4ASWeierstrassPointEquiv (A B : K)
    (hnorm : A^2+A*B+B^2 ≠ 0) :
    (k4ASWeierstrassCurve A B).toAffine.Point ≃
      Option (k4ASWeierstrassPairs A B) := by
  let W := k4ASWeierstrassCurve A B
  letI : W.IsElliptic := by
    simpa [W] using k4ASWeierstrassCurve_isElliptic A B hnorm
  exact W.toAffine.nonsingularPointEquiv.trans
    (Equiv.optionCongr (Equiv.subtypeEquivProp (by
      funext xy
      apply propext
      rw [← WeierstrassCurve.Affine.equation_iff_nonsingular,
        k4ASWeierstrassCurve_equation])))

@[instance_reducible]
noncomputable def k4ASWeierstrassPointFintype (A B : K)
    (hnorm : A^2+A*B+B^2 ≠ 0) :
    Fintype (k4ASWeierstrassCurve A B).toAffine.Point :=
  Fintype.ofEquiv (Option (k4ASWeierstrassPairs A B))
    (k4ASWeierstrassPointEquiv A B hnorm).symm

theorem k4ASWeierstrassCurve_pointCount (A B : K)
    (hnorm : A^2+A*B+B^2 ≠ 0)
    [Fintype (k4ASWeierstrassCurve A B).toAffine.Point] :
    HasseWeil.pointCount (k4ASWeierstrassCurve A B).toAffine =
      (Fintype.card (k4ASWeierstrassPairs A B) : ℝ)+1 := by
  rw [HasseWeil.pointCount,
    Fintype.card_congr (k4ASWeierstrassPointEquiv A B hnorm)]
  simp

theorem k4ASWeierstrassCurve_hasse (A B : K)
    (hnorm : A^2+A*B+B^2 ≠ 0)
    [Fintype (k4ASWeierstrassCurve A B).toAffine.Point] :
    |HasseWeil.pointCount (k4ASWeierstrassCurve A B).toAffine -
        (Fintype.card K : ℝ)-1| ≤ 2*Real.sqrt (Fintype.card K : ℝ) := by
  classical
  let W := k4ASWeierstrassCurve A B
  letI : W.IsElliptic := by
    simpa [W] using k4ASWeierstrassCurve_isElliptic A B hnorm
  simpa [W] using HasseWeil.WeilPairing.hasse_bound W

#print axioms k4ASWeierstrassCurve_pointCount
#print axioms k4ASWeierstrassCurve_hasse
#print axioms k4ASWeierstrassPointFintype
#print axioms k4ASAffinePointToWeierstrassPair

end Finite

end Carlet
end

