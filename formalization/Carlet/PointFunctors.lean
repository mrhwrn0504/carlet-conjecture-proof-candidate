import Carlet.FiniteNaturality
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.NatIso

noncomputable section

open CategoryTheory

namespace Carlet.Quadratic

universe u

def openCarletFunctor (r : ℕ) : CommAlgCat.{u} (ZMod 2) ⥤ Type u where
  obj A := OpenCarletPoint A r
  map f := ↾(mapOpenPoint f.hom.toRingHom r)
  map_id A := by rfl
  map_comp f g := by rfl

def quadraticFunctor (r : ℕ) : CommAlgCat.{u} (ZMod 2) ⥤ Type u where
  obj A := QuadraticPoint A r
  map f := ↾(mapQuadraticPoint f.hom.toRingHom r)
  map_id A := by rfl
  map_comp f g := by rfl

/-- An actual natural isomorphism of finite-coordinate point functors
over all F₂-algebras, not just a family of cardinality equalities. -/
def coordinateNaturalIso (r : ℕ) (hr : 0 < r) :
    openCarletFunctor.{u} r ≅ quadraticFunctor.{u} r :=
  NatIso.ofComponents (fun A => (finiteCoordinateEquiv (A := A) r hr).toIso) (by
    intro A B f
    ext x
    exact (finiteForward_natural f.hom.toRingHom r hr x).symm)

#print axioms openCarletFunctor
#print axioms quadraticFunctor
#print axioms coordinateNaturalIso

end Carlet.Quadratic
