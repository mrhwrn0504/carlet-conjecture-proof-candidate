import Carlet.OpenPolynomial

noncomputable section

open CategoryTheory

namespace Carlet.Quadratic

universe u

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra (ZMod 2) A] [Algebra (ZMod 2) B]

def openPointToHom {r : ℕ} (y : OpenInversePoint A r) : OpenCoordinateRing r →ₐ[ZMod 2] A :=
  Ideal.Quotient.liftₐ (openIdeal r) (openCoordinateEval y.val)
    (fun _ hp => openEval_kills_ideal y hp)

theorem openPointToHom_comp {r : ℕ} (y : OpenInversePoint A r) :
    (openPointToHom y).comp (Ideal.Quotient.mkₐ (ZMod 2) (openIdeal r)) =
      openCoordinateEval y.val := by
  ext p
  rfl

def openHomToPoint {r : ℕ} (f : OpenCoordinateRing r →ₐ[ZMod 2] A) : OpenInversePoint A r := by
  let g := f.comp (Ideal.Quotient.mkₐ (ZMod 2) (openIdeal r))
  refine ⟨openCoordinatesOfHom g, (openRelationExpression_zero_iff _).mp ?_⟩
  intro e
  rw [← openCoordinateEval_relation, openCoordinateEval_coordinatesOfHom]
  change f (Ideal.Quotient.mk (openIdeal r) (openRelationPolynomial r e)) = 0
  have h : Ideal.Quotient.mk (openIdeal r) (openRelationPolynomial r e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e,rfl⟩)
  rw [h, map_zero]

def openHomEquivInversePoint (r : ℕ) :
    (OpenCoordinateRing r →ₐ[ZMod 2] A) ≃ OpenInversePoint A r where
  toFun := openHomToPoint
  invFun := openPointToHom
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    rw [openPointToHom_comp]
    exact openCoordinateEval_coordinatesOfHom _
  right_inv y := by
    apply Subtype.ext
    change openCoordinatesOfHom ((openPointToHom y).comp
      (Ideal.Quotient.mkₐ (ZMod 2) (openIdeal r))) = y.val
    rw [openPointToHom_comp, openCoordinatesOfHom_eval]

def openHomEquivPoint (r : ℕ) :
    (OpenCoordinateRing r →ₐ[ZMod 2] A) ≃ OpenCarletPoint A r :=
  (openHomEquivInversePoint r).trans (openInverseEquiv r).symm

theorem openHomEquivPoint_natural {r : ℕ} (g : A →ₐ[ZMod 2] B)
    (f : OpenCoordinateRing r →ₐ[ZMod 2] A) :
    openHomEquivPoint r (g.comp f) = mapOpenPoint g.toRingHom r (openHomEquivPoint r f) := by
  apply Subtype.ext
  rfl

def openRingHomFunctor (r : ℕ) : CommAlgCat.{u} (ZMod 2) ⥤ Type u where
  obj A := OpenCoordinateRing r →ₐ[ZMod 2] A
  map g := ↾(fun f => g.hom.comp f)
  map_id A := by rfl
  map_comp f g := by rfl

def explicitOpenRepresentation (r : ℕ) :
    openRingHomFunctor.{u} r ≅ openCarletFunctor.{u} r :=
  NatIso.ofComponents (fun A => (openHomEquivPoint (A := A) r).toIso) (by
    intro A B g
    ext f
    exact (openHomEquivPoint_natural g.hom f).symm)

def presentationNaturalIso (r : ℕ) (hr : 0 < r) :
    openRingHomFunctor.{u} r ≅ quadraticRingHomFunctor.{u} r :=
  explicitOpenRepresentation r ≪≫ (openCarletRepresentation r hr).symm

#print axioms openHomEquivPoint
#print axioms explicitOpenRepresentation
#print axioms presentationNaturalIso

end Carlet.Quadratic
