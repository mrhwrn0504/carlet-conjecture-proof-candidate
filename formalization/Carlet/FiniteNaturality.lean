import Carlet.FiniteCoordinates

noncomputable section

open scoped BigOperators

namespace Carlet.Quadratic

variable {A B : Type*} [CommRing A] [CommRing B]

def mapCoordinates (f : A →+* B) {r : ℕ} (y : QuadraticCoordinates A r) :
    QuadraticCoordinates B r where
  c := fun j => f (y.c j)
  t := fun j => f (y.t j)
  d := fun j => f (y.d j)
  u := fun a j => f (y.u a j)

theorem cSeq_mapCoordinates (f : A →+* B) {r : ℕ} (y : QuadraticCoordinates A r) :
    cSeq (mapCoordinates f y) = f ∘ cSeq y := by
  funext j
  by_cases hj : j < r-1 <;> simp [cSeq, mapCoordinates, Function.comp_apply, hj]

theorem tSeq_mapCoordinates (f : A →+* B) {r : ℕ} (y : QuadraticCoordinates A r) :
    tSeq (mapCoordinates f y) = f ∘ tSeq y := by
  funext j
  by_cases h0 : j = 0 <;> by_cases hj : j-1 < r-1 <;>
    simp [tSeq, mapCoordinates, Function.comp_apply, h0, hj]

theorem dSeq_mapCoordinates (f : A →+* B) {r : ℕ} (y : QuadraticCoordinates A r) :
    dSeq (mapCoordinates f y) = f ∘ dSeq y := by
  funext j
  by_cases h0 : j = 0 <;> by_cases hj : j-1 < r-1 <;>
    simp [dSeq, mapCoordinates, Function.comp_apply, h0, hj]

theorem uSeq_mapCoordinates (f : A →+* B) {r : ℕ} (y : QuadraticCoordinates A r) :
    uSeq (mapCoordinates f y) = fun a j => f (uSeq y a j) := by
  funext a j
  by_cases ha : a < r <;> by_cases hj : j < a <;> by_cases he : j = a <;>
    simp [uSeq, mapCoordinates, ha, hj, he]

theorem extendVector_map (f : A →+* B) {r : ℕ} (x : Fin r → A) :
    extendVector (f ∘ x) = f ∘ extendVector x := by
  funext j
  by_cases hj : j < r <;> simp [extendVector, Function.comp_apply, hj]

theorem quadraticCondition_map (f : A →+* B) (c t d : ℕ → A)
    (u : ℕ → ℕ → A) (r : ℕ) (h : QuadraticCondition c t d u r) :
    QuadraticCondition (f ∘ c) (f ∘ t) (f ∘ d) (fun a j => f (u a j)) r := by
  obtain ⟨hu, ht0, htd, hct, hs⟩ := h
  refine ⟨triangularRelations_map f c u r hu, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, map_one] using congrArg f ht0
  · intro j hj
    simpa only [Function.comp_apply, map_mul, map_one] using congrArg f (htd j hj)
  · intro j hj
    simpa only [Function.comp_apply, map_mul] using congrArg f (hct j hj)
  · simpa only [Function.comp_apply, map_sum, map_zero] using congrArg f hs

def mapOpenPoint (f : A →+* B) (r : ℕ) (x : OpenCarletPoint A r) : OpenCarletPoint B r := by
  refine ⟨f ∘ x.val, ?_⟩
  rw [extendVector_map]
  exact openCarletCondition_map f _ r x.property

def mapQuadraticPoint (f : A →+* B) (r : ℕ) (y : QuadraticPoint A r) : QuadraticPoint B r := by
  refine ⟨mapCoordinates f y.val, ?_⟩
  rw [cSeq_mapCoordinates, tSeq_mapCoordinates, dSeq_mapCoordinates, uSeq_mapCoordinates]
  exact quadraticCondition_map f _ _ _ _ r y.property

theorem finiteReverse_natural [Algebra (ZMod 2) A] [Algebra (ZMod 2) B]
    (f : A →+* B) (r : ℕ) (hr : 0 < r) (y : QuadraticPoint A r) :
    finiteReverse r hr (mapQuadraticPoint f r y) = mapOpenPoint f r (finiteReverse r hr y) := by
  apply Subtype.ext
  funext a
  change uSeq (mapCoordinates f y.val) a.val 0 = f (uSeq y.val a.val 0)
  rw [uSeq_mapCoordinates]

/-- The finite coordinate equivalence is natural under base-ring maps.
This still does not assert that the required schemes have been represented. -/
theorem finiteForward_natural [Algebra (ZMod 2) A] [Algebra (ZMod 2) B]
    (f : A →+* B) (r : ℕ) (hr : 0 < r) (x : OpenCarletPoint A r) :
    mapQuadraticPoint f r (finiteForward r hr x) = finiteForward r hr (mapOpenPoint f r x) := by
  apply (finiteCoordinateEquiv (A := B) r hr).symm.injective
  change finiteReverse r hr (mapQuadraticPoint f r (finiteForward r hr x)) =
    finiteReverse r hr (finiteForward r hr (mapOpenPoint f r x))
  rw [finiteReverse_natural, finite_left_inverse, finite_left_inverse]

#print axioms quadraticCondition_map
#print axioms finiteReverse_natural
#print axioms finiteForward_natural

end Carlet.Quadratic
