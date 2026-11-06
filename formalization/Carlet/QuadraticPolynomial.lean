import Carlet.PointFunctors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section

namespace Carlet.Quadratic

abbrev TriangularIndex (r : ℕ) := (a : Fin r) × Fin a.val

abbrev QuadraticVariable (r : ℕ) :=
  Fin (r-1) ⊕ (Fin (r-1) ⊕ (Fin (r-1) ⊕ TriangularIndex r))

abbrev QuadraticPolynomial (r : ℕ) := MvPolynomial (QuadraticVariable r) (ZMod 2)

def universalCoordinates (r : ℕ) : QuadraticCoordinates (QuadraticPolynomial r) r where
  c := fun j => MvPolynomial.X (Sum.inl j)
  t := fun j => MvPolynomial.X (Sum.inr (Sum.inl j))
  d := fun j => MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl j)))
  u := fun a j => MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr ⟨a,j⟩)))

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

def assignment {r : ℕ} (y : QuadraticCoordinates A r) : QuadraticVariable r → A
  | Sum.inl j => y.c j
  | Sum.inr (Sum.inl j) => y.t j
  | Sum.inr (Sum.inr (Sum.inl j)) => y.d j
  | Sum.inr (Sum.inr (Sum.inr ⟨a,j⟩)) => y.u a j

def coordinateEval {r : ℕ} (y : QuadraticCoordinates A r) : QuadraticPolynomial r →ₐ[ZMod 2] A :=
  MvPolynomial.aeval (assignment y)

def coordinatesOfHom {r : ℕ} (f : QuadraticPolynomial r →ₐ[ZMod 2] A) : QuadraticCoordinates A r :=
  mapCoordinates f.toRingHom (universalCoordinates r)

theorem coordinatesOfHom_coordinateEval {r : ℕ} (y : QuadraticCoordinates A r) :
    coordinatesOfHom (coordinateEval y) = y := by
  apply QuadraticCoordinates.ext
  · funext j; simp [coordinatesOfHom, coordinateEval, mapCoordinates, universalCoordinates, assignment]
  · funext j; simp [coordinatesOfHom, coordinateEval, mapCoordinates, universalCoordinates, assignment]
  · funext j; simp [coordinatesOfHom, coordinateEval, mapCoordinates, universalCoordinates, assignment]
  · funext a j; simp [coordinatesOfHom, coordinateEval, mapCoordinates, universalCoordinates, assignment]

theorem coordinateEval_coordinatesOfHom {r : ℕ} (f : QuadraticPolynomial r →ₐ[ZMod 2] A) :
    coordinateEval (coordinatesOfHom f) = f := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with j | j | j | ⟨a,j⟩ <;>
    simp [coordinateEval, coordinatesOfHom, assignment, mapCoordinates, universalCoordinates]

def polynomialHomEquivCoordinates (r : ℕ) :
    (QuadraticPolynomial r →ₐ[ZMod 2] A) ≃ QuadraticCoordinates A r where
  toFun := coordinatesOfHom
  invFun := coordinateEval
  left_inv := coordinateEval_coordinatesOfHom
  right_inv := coordinatesOfHom_coordinateEval

#print axioms polynomialHomEquivCoordinates

end Carlet.Quadratic
