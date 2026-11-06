import Carlet.K4ThetaSpecializationProbe
import Carlet.K4CoeffEightProbe
import Carlet.K4ThetaSpanBridgeProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

omit [Fintype K] [DecidableEq K] in
/-- With the first three coordinates fixed, Θ₄ is the value of their
    three-space subspace polynomial plus the square of its X⁴ coefficient. -/
theorem k4_theta4_eval_eq_three_space_polynomial (x : Fin 4 → K) :
    MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) =
      (k4SpecialP3 x).coeff 4 ^ 2 + (k4SpecialP3 x).eval (x 3) := by
  rw [← k4SpecialPolynomial_coeff_eight x]
  rw [k4SpecialPolynomial, Polynomial.coeff_map, coeff_eight_P4]
  simp only [map_add, map_pow, k4SpecialP3, k4SpecialHom,
    Polynomial.coeff_map, Polynomial.eval_map]
  rw [Polynomial.eval₂_eq_eval_map]
  have heval := k4_map_eval x k4UniversalP3 (k4UniversalX 3)
  rw [k4SpecialHom_X] at heval
  simpa [k4SpecialHom] using heval

omit [Fintype K] [DecidableEq K] in
/-- Exact root criterion for choosing the fourth generator after fixing a
    three-space. -/
theorem k4_theta4_zero_iff_three_space_image (x : Fin 4 → K) :
    MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0 ↔
      (k4SpecialP3 x).eval (x 3) = (k4SpecialP3 x).coeff 4 ^ 2 := by
  rw [k4_theta4_eval_eq_three_space_polynomial]
  constructor
  · intro h
    have h' := add_eq_zero_iff_eq_neg.mp h
    simpa only [CharTwo.neg_eq] using h'.symm
  · intro h
    rw [h, CharTwo.add_self_eq_zero]

omit [Fintype K] [DecidableEq K] in
lemma k4SpecialP3_update_fourth (x : Fin 4 → K) (z : K) :
    k4SpecialP3 (Function.update x 3 z) = k4SpecialP3 x := by
  rw [k4SpecialP3_eq, k4SpecialP3_eq, k4SpecialP2_eq, k4SpecialP2_eq,
    k4SpecialP1_eq, k4SpecialP1_eq]
  simp [Function.update]

omit [Fintype K] [DecidableEq K] in
/-- Once the first three generators are fixed, a Θ₄-zero fourth coordinate
    exists exactly when the square of the X⁴ coefficient belongs to the
    image of their 3-space subspace polynomial. -/
theorem k4_theta4_root_exists_iff_three_space_image (x : Fin 4 → K) :
    (∃ z : K,
      MvPolynomial.eval (Function.update x 3 z)
        (theta4.map (algebraMap (ZMod 2) K)) = 0) ↔
      (k4SpecialP3 x).coeff 4 ^ 2 ∈ Set.range (k4SpecialP3 x).eval := by
  constructor
  · rintro ⟨z, hz⟩
    have hz' := (k4_theta4_zero_iff_three_space_image (Function.update x 3 z)).mp hz
    rw [k4SpecialP3_update_fourth] at hz'
    exact ⟨z, hz'⟩
  · intro h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    apply (k4_theta4_zero_iff_three_space_image (Function.update x 3 z)).mpr
    rw [k4SpecialP3_update_fourth]
    exact hz

lemma k4Span3_polynomial_local (x : Fin 4 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ k4Span1 x) (h2 : x 2 ∉ k4Span2 x) :
    rootProduct (underlyingFinset (k4Span3 x)) = k4SpecialP3 x := by
  have hp1 := k4Span1_polynomial x h0
  have hp2 : rootProduct (underlyingFinset (k4Span2 x)) = k4SpecialP2 x := by
    rw [k4Span2, subspacePolynomial_extension _ _ h1, hp1, k4SpecialP2_eq]
  rw [k4Span3, subspacePolynomial_extension _ _ h2, hp2, k4SpecialP3_eq]

/-- A three-space with nonzero X⁴ coefficient yields a four-dimensional
    zero-sum subspace whenever that coefficient-square lies in the image of
    its subspace polynomial. This isolates the exact remaining k=4
    construction problem as an image-membership problem. -/
theorem hasZeroSumSubspace_four_of_three_space_image
    (x : Fin 4 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ k4Span1 x) (h2 : x 2 ∉ k4Span2 x)
    (hc : (k4SpecialP3 x).coeff 4 ≠ 0)
    (himage : (k4SpecialP3 x).coeff 4 ^ 2 ∈
      Set.range (k4SpecialP3 x).eval) : HasZeroSumSubspace K 4 := by
  obtain ⟨z, hz⟩ := himage
  have hp3 := k4Span3_polynomial_local x h0 h1 h2
  have hroot : (rootProduct (underlyingFinset (k4Span3 x))).eval z =
      (k4SpecialP3 x).coeff 4 ^ 2 := by rw [hp3]; exact hz
  have htarget : (k4SpecialP3 x).coeff 4 ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have h3 : z ∉ k4Span3 x := by
    intro hzmem
    have hz0 := (subspacePolynomial_eval_eq_zero_iff (k4Span3 x) z).mpr hzmem
    rw [hroot] at hz0
    exact htarget hz0
  let x' : Fin 4 → K := Function.update x 3 z
  have h0' : x' 0 ≠ 0 := by simpa [x'] using h0
  have h1' : x' 1 ∉ k4Span1 x' := by simpa [x', k4Span1, Function.update] using h1
  have h2' : x' 2 ∉ k4Span2 x' := by simpa [x', k4Span2, k4Span1, Function.update] using h2
  have h3' : x' 3 ∉ k4Span3 x' := by simpa [x', k4Span3, k4Span2, k4Span1, Function.update] using h3
  have htheta : MvPolynomial.eval x' (theta4.map (algebraMap (ZMod 2) K)) = 0 := by
    apply (k4_theta4_zero_iff_three_space_image x').mpr
    rw [k4SpecialP3_update_fourth]
    simpa [x'] using hz
  exact hasZeroSumSubspace_four_of_theta4_chain x' h0' h1' h2' h3' htheta

#print axioms k4_theta4_eval_eq_three_space_polynomial
#print axioms k4_theta4_zero_iff_three_space_image
#print axioms k4_theta4_root_exists_iff_three_space_image
#print axioms hasZeroSumSubspace_four_of_three_space_image
end Carlet
