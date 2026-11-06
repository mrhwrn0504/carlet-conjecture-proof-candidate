import Carlet.PresentationRingIso
import Mathlib.AlgebraicGeometry.Scheme

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Carlet.Quadratic

/-- Explicit affine presentation of the normalized open equations.
Identification with the reciprocal projective compactification is separate. -/
def openPresentationScheme (r : ℕ) : Scheme := Spec (CommRingCat.of (OpenCoordinateRing r))

def quadraticPresentationScheme (r : ℕ) : Scheme := Spec (CommRingCat.of (QuadraticCoordinateRing r))

def presentationSchemeIso (r : ℕ) (hr : 0 < r) :
    openPresentationScheme r ≅ quadraticPresentationScheme r :=
  (Scheme.Spec.mapIso (presentationRingIso r hr).toRingEquiv.toCommRingCatIso.op).symm

#print axioms presentationSchemeIso

end Carlet.Quadratic
