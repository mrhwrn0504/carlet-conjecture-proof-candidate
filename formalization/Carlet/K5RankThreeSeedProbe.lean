import Carlet.K4AllOddDegreesProbe
import Carlet.K4ThetaCoefficientBridgeProbe
import Carlet.Theta5CoefficientBridgeProbe
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

/-- A rank-four subspace with vanishing X⁸ coefficient contains a rank-three
    subspace with nonzero X⁴ coefficient. -/
theorem rankFour_coeffEight_zero_gives_rankThree_seed
    (V : Submodule (ZMod 2) K) (hV : Module.finrank (ZMod 2) V = 4)
    (hcoeff : (rootProduct (underlyingFinset V)).coeff 8 = 0) :
    ∃ U : Submodule (ZMod 2) K, Module.finrank (ZMod 2) U = 3 ∧
      (rootProduct (underlyingFinset U)).coeff 4 ≠ 0 := by
  classical
  have hthree : 3 ≤ Module.finrank (ZMod 2) V := by rw [hV]; omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod 2) (M := V) (n := 3) hthree
  let g : Fin 3 → K := fun i => (f i : K)
  have hg : LinearIndependent (ZMod 2) g := by
    exact hf.map' V.subtype (LinearMap.ker_eq_bot.mpr V.subtype_injective)
  let U : Submodule (ZMod 2) K := Submodule.span (ZMod 2) (Set.range g)
  have hU : Module.finrank (ZMod 2) U = 3 := by
    simpa [U] using finrank_span_eq_card hg
  have hUV : U ≤ V := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).property
  have hlt : U < V := by
    apply lt_of_le_of_ne hUV
    intro heq
    rw [heq, hV] at hU
    omega
  obtain ⟨v, hvV, hvU⟩ := SetLike.exists_of_lt hlt
  let W := U ⊔ Submodule.span (ZMod 2) ({v} : Set K)
  have hWV : W ≤ V := by
    apply sup_le hUV
    exact (Submodule.span_singleton_le_iff_mem v V).mpr hvV
  have hW : Module.finrank (ZMod 2) W = 4 := by
    dsimp [W]
    rw [extension_finrank U v hvU, hU]
  have hWVeq : W = V := Submodule.eq_of_le_of_finrank_eq hWV (by rw [hW, hV])
  have htop : (rootProduct (underlyingFinset U)).coeff 8 = 1 := by
    have hdeg : (rootProduct (underlyingFinset U)).natDegree = 8 := by
      rw [rootProduct_natDegree, underlyingFinset_card_pow, hU]
      norm_num
    rw [← hdeg]
    exact (rootProduct_monic _).coeff_natDegree
  have hval : (rootProduct (underlyingFinset U)).eval v ≠ 0 := by
    intro hz
    exact hvU ((subspacePolynomial_eval_eq_zero_iff U v).mp hz)
  have hrec := rootProduct_sup_step_coeff_pow U v hvU 2
  have hrec' : (rootProduct (underlyingFinset W)).coeff 8 =
      ((rootProduct (underlyingFinset U)).coeff 4)^2 +
        (rootProduct (underlyingFinset U)).eval v *
          (rootProduct (underlyingFinset U)).coeff 8 := by
    simpa [W] using hrec
  refine ⟨U, hU, ?_⟩
  intro hz
  rw [hWVeq, hcoeff, hz, htop] at hrec'
  simp at hrec'
  exact hval hrec'.symm

theorem exists_rankThree_coeffFour_nonzero_of_odd_card
    (n : ℕ) (hn : Odd n) (hmin : 7 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) :
    ∃ U : Submodule (ZMod 2) K, Module.finrank (ZMod 2) U = 3 ∧
      (rootProduct (underlyingFinset U)).coeff 4 ≠ 0 := by
  have h4 := hasZeroSumSubspace_four_of_odd_card n hn hmin K hcard
  obtain ⟨V, hV, hc⟩ := (hasZeroSumSubspace_four_iff_exists_coeff8 (K := K)).mp h4
  exact rankFour_coeffEight_zero_gives_rankThree_seed V hV hc

#print axioms rankFour_coeffEight_zero_gives_rankThree_seed
#print axioms exists_rankThree_coeffFour_nonzero_of_odd_card
end Carlet
