import Carlet.QuadraticRepresentation

noncomputable section

open scoped BigOperators

namespace Carlet.Quadratic

@[ext] structure OpenInverseCoordinates (A : Type*) (r : ℕ) where
  x : Fin r → A
  v : Bits r → A

variable {A : Type*} [CommRing A]

def OpenInverseCondition {r : ℕ} (y : OpenInverseCoordinates A r) : Prop :=
  extendVector y.x 0 = 1 ∧ y.v (zeroBits r) = 0 ∧
  (∀ b : Bits r, b ≠ zeroBits r → combination (extendVector y.x) r b * y.v b = 1) ∧
  (∑ b : Bits r, y.v b) = 0

abbrev OpenInversePoint (A : Type*) [CommRing A] (r : ℕ) :=
  {y : OpenInverseCoordinates A r // OpenInverseCondition y}

theorem inverse_eq_of_mul_eq_one (a b : A) (h : a * b = 1) : Ring.inverse a = b := by
  have hu : IsUnit a := coordinate_isUnit a b h
  calc
    Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel a hu, one_mul]

theorem inverseCoordinates_canonical {r : ℕ} (y : OpenInversePoint A r) (b : Bits r) :
    y.val.v b = Ring.inverse (combination (extendVector y.val.x) r b) := by
  by_cases hb : b = zeroBits r
  · subst b
    rw [y.property.2.1, combination_zeroBits, Ring.inverse_zero]
  · exact (inverse_eq_of_mul_eq_one _ _ (y.property.2.2.1 b hb)).symm

def openToInverse {r : ℕ} (x : OpenCarletPoint A r) : OpenInversePoint A r := by
  refine ⟨⟨x.val, fun b => Ring.inverse (combination (extendVector x.val) r b)⟩,
    x.property.1, ?_, ?_, x.property.2.2⟩
  · simp only [combination_zeroBits, Ring.inverse_zero]
  · intro b hb
    exact Ring.mul_inverse_cancel _ (x.property.2.1 b hb)

def inverseToOpen {r : ℕ} (y : OpenInversePoint A r) : OpenCarletPoint A r := by
  refine ⟨y.val.x, y.property.1, ?_, ?_⟩
  · intro b hb
    exact coordinate_isUnit _ _ (y.property.2.2.1 b hb)
  · change (∑ b : Bits r, Ring.inverse (combination (extendVector y.val.x) r b)) = 0
    simpa only [← inverseCoordinates_canonical y] using y.property.2.2.2

def openInverseEquiv (r : ℕ) : OpenCarletPoint A r ≃ OpenInversePoint A r where
  toFun := openToInverse
  invFun := inverseToOpen
  left_inv _ := by rfl
  right_inv y := by
    apply Subtype.ext
    apply OpenInverseCoordinates.ext
    · rfl
    · funext b
      exact (inverseCoordinates_canonical y b).symm

#print axioms openInverseEquiv

end Carlet.Quadratic
