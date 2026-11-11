import Carlet.ReverseCarlet

noncomputable section

open Polynomial
open scoped BigOperators Ring

namespace Carlet.Quadratic

variable {A B : Type*} [CommRing A] [CommRing B]

theorem scale_map (f : A →+* B) (c : ℕ → A) (n : ℕ) :
    f (scale c n) = scale (f ∘ c) n := by
  induction n with
  | zero => simp [scale]
  | succ n ih => simp [scale, map_mul, map_pow, ih, Function.comp_apply]

theorem linearScale_map (f : A →+* B) (c : ℕ → A) (n : ℕ) :
    f (linearScale c n) = linearScale (f ∘ c) n := by
  induction n with
  | zero => simp [linearScale]
  | succ n ih => simp [linearScale, map_mul, scale_map, ih]

theorem reconstructedPolynomial_map (f : A →+* B) (c : ℕ → A) (n : ℕ) :
    (reconstructedPolynomial c n).map f = reconstructedPolynomial (f ∘ c) n := by
  induction n with
  | zero => simp [reconstructedPolynomial]
  | succ n ih =>
    simp only [reconstructedPolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_C, ih]
    rw [scale_map f c n]

theorem combination_map (f : A →+* B) (x : ℕ → A) (n : ℕ) (b : Bits n) :
    f (combination x n b) = combination (f ∘ x) n b := by
  induction n with
  | zero => simp [combination]
  | succ n ih =>
    rcases b with ⟨b, flag⟩
    cases flag <;> simp [combination, map_add, ih, Function.comp_apply]

theorem indexedProduct_map (f : A →+* B) (x : ℕ → A) (n : ℕ) :
    (indexedProduct x n).map f = indexedProduct (f ∘ x) n := by
  simp only [indexedProduct, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro b hb
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rw [combination_map f x n b]

/-- The chosen ring inverse is natural on units. No such claim is made
for arbitrary nonunits, for which totalized inverse need not be natural. -/
theorem inverse_map_of_isUnit (f : A →+* B) (a : A) (ha : IsUnit a) :
    f (Ring.inverse a) = Ring.inverse (f a) := by
  apply (ha.map f).mul_left_cancel
  rw [← map_mul, Ring.mul_inverse_cancel _ ha, map_one,
    Ring.mul_inverse_cancel _ (ha.map f)]

theorem fullRank_map (f : A →+* B) (x : ℕ → A) (r : ℕ)
    (h : ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination x r b)) :
    ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination (f ∘ x) r b) := by
  intro b hb
  rw [← combination_map]
  exact (h b hb).map f

theorem fullReciprocalSum_map (f : A →+* B) (x : ℕ → A) (r : ℕ)
    (h : ∀ b : Bits r, b ≠ zeroBits r → IsUnit (combination x r b)) :
    f (fullReciprocalSum x r) = fullReciprocalSum (f ∘ x) r := by
  classical
  simp only [fullReciprocalSum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hz : b = zeroBits r
  · subst b
    simp only [combination_zeroBits, Ring.inverse_zero, map_zero]
  · rw [← combination_map]
    exact inverse_map_of_isUnit f _ (h b hz)

theorem triangularRelations_map (f : A →+* B) (c : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ)
    (h : TriangularRelations c u r) :
    TriangularRelations (f ∘ c) (fun a j => f (u a j)) r := by
  constructor
  · intro a ha
    change f (u a a) = 1
    rw [h.1 a ha, map_one]
  · intro a ha j hj
    simpa only [map_add, map_pow, map_mul, Function.comp_apply] using
      congrArg f (h.2 a ha j hj)

#print axioms reconstructedPolynomial_map
#print axioms indexedProduct_map
#print axioms fullReciprocalSum_map
#print axioms triangularRelations_map

end Carlet.Quadratic
