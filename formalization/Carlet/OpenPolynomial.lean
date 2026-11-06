import Carlet.OpenInverseCoordinates

noncomputable section

open scoped BigOperators

namespace Carlet.Quadratic

abbrev OpenVariable (r : ℕ) := Fin r ⊕ Bits r
abbrev OpenPolynomial (r : ℕ) := MvPolynomial (OpenVariable r) (ZMod 2)

def universalOpenCoordinates (r : ℕ) : OpenInverseCoordinates (OpenPolynomial r) r where
  x j := MvPolynomial.X (Sum.inl j)
  v b := MvPolynomial.X (Sum.inr b)

variable {A B : Type*} [CommRing A] [CommRing B]

def mapOpenCoordinates (f : A →+* B) {r : ℕ} (y : OpenInverseCoordinates A r) :
    OpenInverseCoordinates B r where
  x := f ∘ y.x
  v := f ∘ y.v

abbrev OpenRelation (r : ℕ) := Unit ⊕ (Unit ⊕ ({b : Bits r // b ≠ zeroBits r} ⊕ Unit))

def openRelationExpression {r : ℕ} (y : OpenInverseCoordinates A r) : OpenRelation r → A
  | Sum.inl _ => extendVector y.x 0 - 1
  | Sum.inr (Sum.inl _) => y.v (zeroBits r)
  | Sum.inr (Sum.inr (Sum.inl b)) => combination (extendVector y.x) r b.val * y.v b.val - 1
  | Sum.inr (Sum.inr (Sum.inr _)) => ∑ b : Bits r, y.v b

theorem openRelationExpression_zero_iff {r : ℕ} (y : OpenInverseCoordinates A r) :
    (∀ e, openRelationExpression y e = 0) ↔ OpenInverseCondition y := by
  constructor
  · intro h
    exact ⟨sub_eq_zero.mp (h (Sum.inl ())), h (Sum.inr (Sum.inl ())),
      fun b hb => sub_eq_zero.mp (h (Sum.inr (Sum.inr (Sum.inl ⟨b,hb⟩)))),
      h (Sum.inr (Sum.inr (Sum.inr ())))⟩
  · rintro ⟨hx,h0,hi,hs⟩ e
    rcases e with k | k | b | k
    · exact sub_eq_zero.mpr hx
    · exact h0
    · exact sub_eq_zero.mpr (hi b.val b.property)
    · exact hs

theorem openRelationExpression_map (f : A →+* B) {r : ℕ} (y : OpenInverseCoordinates A r)
    (e : OpenRelation r) :
    openRelationExpression (mapOpenCoordinates f y) e = f (openRelationExpression y e) := by
  rcases e with k | k | b | k
  · simp only [openRelationExpression, mapOpenCoordinates, extendVector_map,
      Function.comp_apply, map_sub, map_one]
  · rfl
  · simp only [openRelationExpression, mapOpenCoordinates, extendVector_map,
      combination_map, Function.comp_apply, map_sub, map_mul, map_one]
  · simp only [openRelationExpression, mapOpenCoordinates, Function.comp_apply, map_sum]

variable [Algebra (ZMod 2) A]

def openCoordinateEval {r : ℕ} (y : OpenInverseCoordinates A r) :
    OpenPolynomial r →ₐ[ZMod 2] A :=
  MvPolynomial.aeval (Sum.elim y.x y.v)

def openCoordinatesOfHom {r : ℕ} (f : OpenPolynomial r →ₐ[ZMod 2] A) :
    OpenInverseCoordinates A r := mapOpenCoordinates f.toRingHom (universalOpenCoordinates r)

theorem openCoordinatesOfHom_eval {r : ℕ} (y : OpenInverseCoordinates A r) :
    openCoordinatesOfHom (openCoordinateEval y) = y := by
  apply OpenInverseCoordinates.ext
  · funext j
    simp [openCoordinatesOfHom, openCoordinateEval, mapOpenCoordinates, universalOpenCoordinates]
  · funext b
    simp [openCoordinatesOfHom, openCoordinateEval, mapOpenCoordinates, universalOpenCoordinates]

theorem openCoordinateEval_coordinatesOfHom {r : ℕ} (f : OpenPolynomial r →ₐ[ZMod 2] A) :
    openCoordinateEval (openCoordinatesOfHom f) = f := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with j | b <;>
    simp [openCoordinateEval, openCoordinatesOfHom, mapOpenCoordinates, universalOpenCoordinates]

def openRelationPolynomial (r : ℕ) := openRelationExpression (universalOpenCoordinates r)

theorem openCoordinateEval_relation {r : ℕ} (y : OpenInverseCoordinates A r) (e : OpenRelation r) :
    openCoordinateEval y (openRelationPolynomial r e) = openRelationExpression y e := by
  have h := openRelationExpression_map (openCoordinateEval y).toRingHom (universalOpenCoordinates r) e
  change openRelationExpression (openCoordinatesOfHom (openCoordinateEval y)) e =
    openCoordinateEval y (openRelationPolynomial r e) at h
  rw [openCoordinatesOfHom_eval] at h
  exact h.symm

def openIdeal (r : ℕ) : Ideal (OpenPolynomial r) := Ideal.span (Set.range (openRelationPolynomial r))
abbrev OpenCoordinateRing (r : ℕ) := OpenPolynomial r ⧸ openIdeal r

theorem openEval_kills_ideal {r : ℕ} (y : OpenInversePoint A r) :
    openIdeal r ≤ RingHom.ker (openCoordinateEval y.val).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨e,rfl⟩
  change openCoordinateEval y.val (openRelationPolynomial r e) = 0
  rw [openCoordinateEval_relation]
  exact (openRelationExpression_zero_iff y.val).mpr y.property e

#print axioms openRelationExpression_zero_iff
#print axioms openEval_kills_ideal

end Carlet.Quadratic
