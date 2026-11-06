import Carlet.QuadraticRelations

noncomputable section

open CategoryTheory

namespace Carlet.Quadratic

universe u

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

def pointToQuotientHom {r : ℕ} (y : QuadraticPoint A r) :
    QuadraticCoordinateRing r →ₐ[ZMod 2] A :=
  Ideal.Quotient.liftₐ (quadraticIdeal r) (coordinateEval y.val)
    (fun _ hp => coordinateEval_kills_ideal y hp)

theorem pointToQuotientHom_comp {r : ℕ} (y : QuadraticPoint A r) :
    (pointToQuotientHom y).comp (Ideal.Quotient.mkₐ (ZMod 2) (quadraticIdeal r)) =
      coordinateEval y.val := by
  ext p
  rfl

def quotientHomToPoint {r : ℕ} (f : QuadraticCoordinateRing r →ₐ[ZMod 2] A) :
    QuadraticPoint A r := by
  let g := f.comp (Ideal.Quotient.mkₐ (ZMod 2) (quadraticIdeal r))
  refine ⟨coordinatesOfHom g, (relationExpression_zero_iff _).mp ?_⟩
  intro e
  rw [← coordinateEval_relation, coordinateEval_coordinatesOfHom]
  change f (Ideal.Quotient.mk (quadraticIdeal r) (relationPolynomial r e)) = 0
  have h : Ideal.Quotient.mk (quadraticIdeal r) (relationPolynomial r e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e,rfl⟩)
  rw [h, map_zero]

theorem quotientHomToPoint_pointToQuotientHom {r : ℕ} (y : QuadraticPoint A r) :
    quotientHomToPoint (pointToQuotientHom y) = y := by
  apply Subtype.ext
  change coordinatesOfHom ((pointToQuotientHom y).comp
    (Ideal.Quotient.mkₐ (ZMod 2) (quadraticIdeal r))) = y.val
  rw [pointToQuotientHom_comp, coordinatesOfHom_coordinateEval]

theorem pointToQuotientHom_quotientHomToPoint {r : ℕ}
    (f : QuadraticCoordinateRing r →ₐ[ZMod 2] A) :
    pointToQuotientHom (quotientHomToPoint f) = f := by
  apply Ideal.Quotient.algHom_ext
  rw [pointToQuotientHom_comp]
  exact coordinateEval_coordinatesOfHom _

def quotientHomEquivPoint (r : ℕ) :
    (QuadraticCoordinateRing r →ₐ[ZMod 2] A) ≃ QuadraticPoint A r where
  toFun := quotientHomToPoint
  invFun := pointToQuotientHom
  left_inv := pointToQuotientHom_quotientHomToPoint
  right_inv := quotientHomToPoint_pointToQuotientHom

variable {B : Type*} [CommRing B] [Algebra (ZMod 2) B]

theorem quotientHomToPoint_natural {r : ℕ} (g : A →ₐ[ZMod 2] B)
    (f : QuadraticCoordinateRing r →ₐ[ZMod 2] A) :
    quotientHomToPoint (g.comp f) = mapQuadraticPoint g.toRingHom r (quotientHomToPoint f) := by
  apply Subtype.ext
  rfl

/-- The hom functor of the explicit quotient algebra, with no geometric assumptions. -/
def quadraticRingHomFunctor (r : ℕ) : CommAlgCat.{u} (ZMod 2) ⥤ Type u where
  obj A := QuadraticCoordinateRing r →ₐ[ZMod 2] A
  map g := ↾(fun f => g.hom.comp f)
  map_id A := by rfl
  map_comp f g := by rfl

def quadraticRepresentation (r : ℕ) :
    quadraticRingHomFunctor.{u} r ≅ quadraticFunctor.{u} r :=
  CategoryTheory.NatIso.ofComponents
    (fun A => (quotientHomEquivPoint (A := A) r).toIso) (by
      intro A B g
      ext f
      exact (quotientHomToPoint_natural g.hom f).symm)

def openCarletRepresentation (r : ℕ) (hr : 0 < r) :
    quadraticRingHomFunctor.{u} r ≅ openCarletFunctor.{u} r :=
  quadraticRepresentation r ≪≫ (coordinateNaturalIso r hr).symm

#print axioms quotientHomEquivPoint
#print axioms quadraticRepresentation
#print axioms openCarletRepresentation

end Carlet.Quadratic
