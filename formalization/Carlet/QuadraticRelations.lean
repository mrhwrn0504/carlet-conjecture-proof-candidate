import Carlet.QuadraticPolynomial
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

open scoped BigOperators

namespace Carlet.Quadratic

abbrev QuadraticRelation (r : ℕ) :=
  TriangularIndex r ⊕ (Fin (r-1) ⊕ (Fin (r-1) ⊕ Unit))

variable {A B : Type*} [CommRing A] [CommRing B]

def relationExpression {r : ℕ} (y : QuadraticCoordinates A r) : QuadraticRelation r → A
  | Sum.inl ⟨a,j⟩ =>
      uSeq y a.val j.val ^ 2 + uSeq y a.val j.val -
        cSeq y j.val * uSeq y a.val (j.val+1)
  | Sum.inr (Sum.inl j) => y.t j * y.d j - 1
  | Sum.inr (Sum.inr (Sum.inl j)) => y.c j * y.t j - tSeq y j.val
  | Sum.inr (Sum.inr (Sum.inr _)) => ∑ j ∈ Finset.range r, tSeq y j

def relationPolynomial (r : ℕ) : QuadraticRelation r → QuadraticPolynomial r :=
  relationExpression (universalCoordinates r)

theorem relationExpression_map (f : A →+* B) {r : ℕ} (y : QuadraticCoordinates A r)
    (e : QuadraticRelation r) :
    relationExpression (mapCoordinates f y) e = f (relationExpression y e) := by
  rcases e with ⟨a,j⟩ | j | j | k
  · simp only [relationExpression, uSeq_mapCoordinates, cSeq_mapCoordinates,
      Function.comp_apply, map_sub, map_pow, map_add, map_mul]
  · simp only [relationExpression, mapCoordinates, map_sub, map_mul, map_one]
  · simp only [relationExpression, tSeq_mapCoordinates, Function.comp_apply]
    simp only [mapCoordinates, map_sub, map_mul]
  · simp only [relationExpression, tSeq_mapCoordinates, Function.comp_apply, map_sum]

theorem relationExpression_zero_iff {r : ℕ} (y : QuadraticCoordinates A r) :
    (∀ e, relationExpression y e = 0) ↔
      QuadraticCondition (cSeq y) (tSeq y) (dSeq y) (uSeq y) r := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro a ha
      simp [uSeq, ha]
    · intro a ha j hj
      exact sub_eq_zero.mp (h (Sum.inl ⟨⟨a,ha⟩,⟨j,hj⟩⟩))
    · simp [tSeq]
    · intro j hj
      by_cases h0 : j = 0
      · subst j; simp [tSeq, dSeq]
      · let i : Fin (r-1) := ⟨j-1, by omega⟩
        have he : j = i.val+1 := by dsimp [i]; omega
        rw [he, tSeq_apply, dSeq_apply]
        exact sub_eq_zero.mp (h (Sum.inr (Sum.inl i)))
    · intro j hj
      let i : Fin (r-1) := ⟨j, by omega⟩
      change cSeq y i.val * tSeq y (i.val+1) = tSeq y i.val
      rw [cSeq_apply, tSeq_apply]
      exact sub_eq_zero.mp (h (Sum.inr (Sum.inr (Sum.inl i))))
    · exact h (Sum.inr (Sum.inr (Sum.inr ())))
  · intro h e
    rcases e with ⟨a,j⟩ | j | j | k
    · exact sub_eq_zero.mpr (h.1.2 a.val a.isLt j.val j.isLt)
    · have hi := h.2.2.1 (j.val+1) (by omega)
      rw [tSeq_apply, dSeq_apply] at hi
      exact sub_eq_zero.mpr hi
    · have hi := h.2.2.2.1 j.val (by omega)
      rw [cSeq_apply, tSeq_apply] at hi
      exact sub_eq_zero.mpr hi
    · exact h.2.2.2.2

variable [Algebra (ZMod 2) A]

theorem coordinateEval_relation {r : ℕ} (y : QuadraticCoordinates A r) (e : QuadraticRelation r) :
    coordinateEval y (relationPolynomial r e) = relationExpression y e := by
  have h := relationExpression_map (coordinateEval y).toRingHom (universalCoordinates r) e
  change relationExpression (coordinatesOfHom (coordinateEval y)) e =
    coordinateEval y (relationPolynomial r e) at h
  rw [coordinatesOfHom_coordinateEval] at h
  exact h.symm

def quadraticIdeal (r : ℕ) : Ideal (QuadraticPolynomial r) :=
  Ideal.span (Set.range (relationPolynomial r))

abbrev QuadraticCoordinateRing (r : ℕ) := QuadraticPolynomial r ⧸ quadraticIdeal r

theorem quadraticIdeal_le_ker_iff {r : ℕ} (f : QuadraticPolynomial r →ₐ[ZMod 2] A) :
    quadraticIdeal r ≤ RingHom.ker f.toRingHom ↔ ∀ e, f (relationPolynomial r e) = 0 := by
  constructor
  · intro h e
    exact h (Ideal.subset_span ⟨e,rfl⟩)
  · intro h
    apply Ideal.span_le.mpr
    rintro p ⟨e,rfl⟩
    exact h e

theorem coordinateEval_kills_ideal {r : ℕ} (y : QuadraticPoint A r) :
    quadraticIdeal r ≤ RingHom.ker (coordinateEval y.val).toRingHom := by
  apply (quadraticIdeal_le_ker_iff (coordinateEval y.val)).mpr
  intro e
  rw [coordinateEval_relation]
  exact (relationExpression_zero_iff y.val).mpr y.property e

#print axioms relationExpression_zero_iff
#print axioms coordinateEval_kills_ideal

end Carlet.Quadratic
