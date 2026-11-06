import Carlet.OpenRepresentation

noncomputable section

namespace Carlet.Quadratic

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra (ZMod 2) A] [Algebra (ZMod 2) B]

def presentationEquiv (r : ℕ) (hr : 0 < r) :
    (OpenCoordinateRing r →ₐ[ZMod 2] A) ≃ (QuadraticCoordinateRing r →ₐ[ZMod 2] A) :=
  (openHomEquivPoint r).trans
    ((finiteCoordinateEquiv r hr).trans (quotientHomEquivPoint r).symm)

theorem presentationEquiv_natural (r : ℕ) (hr : 0 < r) (g : A →ₐ[ZMod 2] B)
    (f : OpenCoordinateRing r →ₐ[ZMod 2] A) :
    presentationEquiv r hr (g.comp f) = g.comp (presentationEquiv r hr f) := by
  apply (quotientHomEquivPoint r).injective
  change quotientHomToPoint (pointToQuotientHom
      (finiteForward r hr (openHomEquivPoint r (g.comp f)))) =
    quotientHomToPoint (g.comp (pointToQuotientHom
      (finiteForward r hr (openHomEquivPoint r f))))
  rw [quotientHomToPoint_natural, quotientHomToPoint_pointToQuotientHom,
    quotientHomToPoint_pointToQuotientHom,
    openHomEquivPoint_natural, finiteForward_natural]

theorem presentationEquiv_symm_natural (r : ℕ) (hr : 0 < r) (g : A →ₐ[ZMod 2] B)
    (f : QuadraticCoordinateRing r →ₐ[ZMod 2] A) :
    (presentationEquiv r hr).symm (g.comp f) =
      g.comp ((presentationEquiv r hr).symm f) := by
  apply (presentationEquiv r hr).injective
  rw [Equiv.apply_symm_apply, presentationEquiv_natural, Equiv.apply_symm_apply]

def quadraticToOpenRing (r : ℕ) (hr : 0 < r) :
    QuadraticCoordinateRing r →ₐ[ZMod 2] OpenCoordinateRing r :=
  presentationEquiv r hr (AlgHom.id (ZMod 2) (OpenCoordinateRing r))

def openToQuadraticRing (r : ℕ) (hr : 0 < r) :
    OpenCoordinateRing r →ₐ[ZMod 2] QuadraticCoordinateRing r :=
  (presentationEquiv r hr).symm (AlgHom.id (ZMod 2) (QuadraticCoordinateRing r))

theorem openToQuadratic_comp_quadraticToOpen (r : ℕ) (hr : 0 < r) :
    (openToQuadraticRing r hr).comp (quadraticToOpenRing r hr) =
      AlgHom.id (ZMod 2) (QuadraticCoordinateRing r) := by
  rw [quadraticToOpenRing, ← presentationEquiv_natural]
  simp only [AlgHom.comp_id, openToQuadraticRing, Equiv.apply_symm_apply]

theorem quadraticToOpen_comp_openToQuadratic (r : ℕ) (hr : 0 < r) :
    (quadraticToOpenRing r hr).comp (openToQuadraticRing r hr) =
      AlgHom.id (ZMod 2) (OpenCoordinateRing r) := by
  rw [openToQuadraticRing, ← presentationEquiv_symm_natural]
  simp only [AlgHom.comp_id, quadraticToOpenRing, Equiv.symm_apply_apply]

def presentationRingIso (r : ℕ) (hr : 0 < r) :
    OpenCoordinateRing r ≃ₐ[ZMod 2] QuadraticCoordinateRing r :=
  AlgEquiv.ofAlgHom (openToQuadraticRing r hr) (quadraticToOpenRing r hr)
    (openToQuadratic_comp_quadraticToOpen r hr) (quadraticToOpen_comp_openToQuadratic r hr)

#print axioms presentationRingIso

end Carlet.Quadratic
