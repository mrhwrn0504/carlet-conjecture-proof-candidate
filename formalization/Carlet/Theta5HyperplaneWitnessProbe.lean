import Carlet.Theta5FinitePointValuesProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

/-- Every binary linear hyperplane contains a point where Θ₅ is nonzero. -/
theorem theta5_f2_hyperplane_has_nonzero_value (r : Fin 5 → ZMod 2) :
    ∃ x : Fin 5 → ZMod 2, (∑ i, r i * x i) = 0 ∧ MvPolynomial.eval x theta5 ≠ 0 := by
  classical
  by_cases h : ∃ i, r i = 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
    · simp [hi]
    · rw [theta5_eval_unit]
      exact one_ne_zero
  · have hall (i : Fin 5) : r i = 1 := by
      have hi : r i ≠ 0 := by
        intro hz
        exact h ⟨i, hz⟩
      have h01 (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
        fin_cases a
        · exact False.elim (ha rfl)
        · rfl
      exact h01 (r i) hi
    refine ⟨fun k => if k = 0 ∨ k = 1 then 1 else 0, ?_, ?_⟩
    · simp [hall]
      decide
    · rw [theta5_eval_two_distinct_units 0 1 (by decide)]
      exact one_ne_zero

def theta5F2Linear (r : Fin 5 → ZMod 2) : MvPolynomial (Fin 5) (ZMod 2) :=
  ∑ i, MvPolynomial.C (r i) * MvPolynomial.X i

/-- No binary linear form divides Θ₅, including the zero form. -/
theorem theta5_no_f2_linear_factor (r : Fin 5 → ZMod 2) :
    ¬ theta5F2Linear r ∣ theta5 := by
  obtain ⟨x, hx, hnz⟩ := theta5_f2_hyperplane_has_nonzero_value r
  rintro ⟨g, hg⟩
  apply hnz
  rw [hg, MvPolynomial.eval_mul]
  have he : MvPolynomial.eval x (theta5F2Linear r) = 0 := by
    simpa [theta5F2Linear] using hx
  simp [he]

/-- The same witness remains valid after extending scalars to any field
    of characteristic two equipped with the displayed algebra structure. -/
theorem theta5_field_hyperplane_has_value_one
    {K : Type*} [Field K] [Algebra (ZMod 2) K] (r : Fin 5 → ZMod 2) :
    ∃ y : Fin 5 → K,
      (∑ i, algebraMap (ZMod 2) K (r i) * y i) = 0 ∧
      MvPolynomial.eval y (theta5.map (algebraMap (ZMod 2) K)) = 1 := by
  obtain ⟨x, hx, hnz⟩ := theta5_f2_hyperplane_has_nonzero_value r
  have ht : MvPolynomial.eval x theta5 = 1 := by
    generalize hz : MvPolynomial.eval x theta5 = a at hnz ⊢
    fin_cases a
    · exact False.elim (hnz rfl)
    · rfl
  let f := algebraMap (ZMod 2) K
  refine ⟨fun i => f (x i), ?_, ?_⟩
  · have hh := congrArg f hx
    simpa only [map_sum, map_mul, map_zero] using hh
  · have hh := (MvPolynomial.map_eval f x theta5).symm
    simpa [ht, Function.comp_def] using hh

theorem theta5_no_binary_linear_factor_over_field
    {K : Type*} [Field K] [Algebra (ZMod 2) K] (r : Fin 5 → ZMod 2) :
    ¬ (theta5F2Linear r).map (algebraMap (ZMod 2) K) ∣
      theta5.map (algebraMap (ZMod 2) K) := by
  obtain ⟨y, hy, htheta⟩ := theta5_field_hyperplane_has_value_one (K := K) r
  rintro ⟨g, hg⟩
  have he : MvPolynomial.eval y ((theta5F2Linear r).map (algebraMap (ZMod 2) K)) = 0 := by
    simpa [theta5F2Linear, MvPolynomial.eval_map] using hy
  have hh := congrArg (MvPolynomial.eval y) hg
  rw [MvPolynomial.eval_mul, he, zero_mul, htheta] at hh
  exact one_ne_zero hh

#print axioms theta5_f2_hyperplane_has_nonzero_value
#print axioms theta5_no_f2_linear_factor
#print axioms theta5_field_hyperplane_has_value_one
#print axioms theta5_no_binary_linear_factor_over_field
end Carlet
