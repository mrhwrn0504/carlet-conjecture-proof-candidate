import Carlet.Theta5SpecializationBridgeProbe
import Carlet.Theta5CoefficientBridgeProbe

noncomputable section
set_option maxRecDepth 10000
open Polynomial
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def theta5SpecialP1 (x : Fin 5 → K) : Polynomial K :=
  t5EvalP1.map (theta5SpecialHom x)
def theta5SpecialP2 (x : Fin 5 → K) : Polynomial K :=
  t5EvalP2.map (theta5SpecialHom x)
def theta5SpecialP3 (x : Fin 5 → K) : Polynomial K :=
  t5EvalP3.map (theta5SpecialHom x)

omit [Fintype K] [DecidableEq K] in
theorem theta5SpecialP1_eq (x : Fin 5 → K) :
    theta5SpecialP1 x = Polynomial.X ^ 2 + Polynomial.C (x 0) * Polynomial.X := by
  simp [theta5SpecialP1, t5EvalP1, theta5SpecialHom_X]

omit [Fintype K] [DecidableEq K] in
theorem theta5SpecialP2_eq (x : Fin 5 → K) :
    theta5SpecialP2 x = theta5SpecialP1 x ^ 2 +
      Polynomial.C ((theta5SpecialP1 x).eval (x 1)) * theta5SpecialP1 x := by
  simp only [theta5SpecialP2, t5EvalP2, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, theta5_map_eval,
    theta5SpecialHom_X, theta5SpecialP1]

omit [Fintype K] [DecidableEq K] in
theorem theta5SpecialP3_eq (x : Fin 5 → K) :
    theta5SpecialP3 x = theta5SpecialP2 x ^ 2 +
      Polynomial.C ((theta5SpecialP2 x).eval (x 2)) * theta5SpecialP2 x := by
  simp only [theta5SpecialP3, t5EvalP3, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, theta5_map_eval,
    theta5SpecialHom_X, theta5SpecialP2]

omit [Fintype K] [DecidableEq K] in
theorem theta5SpecialP4_eq (x : Fin 5 → K) :
    theta5SpecialP4 x = theta5SpecialP3 x ^ 2 +
      Polynomial.C ((theta5SpecialP3 x).eval (x 3)) * theta5SpecialP3 x := by
  simp only [theta5SpecialP4, t5EvalP4, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, theta5_map_eval,
    theta5SpecialHom_X, theta5SpecialP3]

def theta5Span1 (x : Fin 5 → K) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) ({x 0} : Set K)
def theta5Span2 (x : Fin 5 → K) : Submodule (ZMod 2) K :=
  theta5Span1 x ⊔ Submodule.span (ZMod 2) ({x 1} : Set K)
def theta5Span3 (x : Fin 5 → K) : Submodule (ZMod 2) K :=
  theta5Span2 x ⊔ Submodule.span (ZMod 2) ({x 2} : Set K)
def theta5Span4 (x : Fin 5 → K) : Submodule (ZMod 2) K :=
  theta5Span3 x ⊔ Submodule.span (ZMod 2) ({x 3} : Set K)

theorem theta5Span1_polynomial (x : Fin 5 → K) (h0 : x 0 ≠ 0) :
    rootProduct (underlyingFinset (theta5Span1 x)) = theta5SpecialP1 x := by
  have hb : underlyingFinset (⊥ : Submodule (ZMod 2) K) = {0} := by
    ext y
    simp
  have hp : rootProduct (underlyingFinset (⊥ : Submodule (ZMod 2) K)) =
      (Polynomial.X : Polynomial K) := by simp [hb, rootProduct]
  have hnot : x 0 ∉ (⊥ : Submodule (ZMod 2) K) := by simpa using h0
  have he := subspacePolynomial_extension (⊥ : Submodule (ZMod 2) K) (x 0) hnot
  rw [bot_sup_eq, hp] at he
  simpa [theta5Span1, theta5SpecialP1_eq] using he

theorem theta5Span4_polynomial (x : Fin 5 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ theta5Span1 x) (h2 : x 2 ∉ theta5Span2 x)
    (h3 : x 3 ∉ theta5Span3 x) :
    rootProduct (underlyingFinset (theta5Span4 x)) = theta5SpecialP4 x := by
  have hp1 := theta5Span1_polynomial x h0
  have hp2 : rootProduct (underlyingFinset (theta5Span2 x)) = theta5SpecialP2 x := by
    rw [theta5Span2, subspacePolynomial_extension _ _ h1, hp1, theta5SpecialP2_eq]
  have hp3 : rootProduct (underlyingFinset (theta5Span3 x)) = theta5SpecialP3 x := by
    rw [theta5Span3, subspacePolynomial_extension _ _ h2, hp2, theta5SpecialP3_eq]
  rw [theta5Span4, subspacePolynomial_extension _ _ h3, hp3, theta5SpecialP4_eq]

omit [DecidableEq K] in
theorem theta5Span4_rank (x : Fin 5 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ theta5Span1 x) (h2 : x 2 ∉ theta5Span2 x)
    (h3 : x 3 ∉ theta5Span3 x) :
    Module.finrank (ZMod 2) (theta5Span4 x) = 4 := by
  have hr1 : Module.finrank (ZMod 2) (theta5Span1 x) = 1 :=
    finrank_span_singleton (K := ZMod 2) (V := K) h0
  rw [theta5Span4, extension_finrank _ _ h3, theta5Span3,
    extension_finrank _ _ h2, theta5Span2, extension_finrank _ _ h1, hr1]

theorem theta5_specialization_eq_span_polynomial (x : Fin 5 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ theta5Span1 x) (h2 : x 2 ∉ theta5Span2 x)
    (h3 : x 3 ∉ theta5Span3 x) :
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) =
      (rootProduct (underlyingFinset (theta5Span4 x))).coeff 8 ^ 2 +
      (rootProduct (underlyingFinset (theta5Span4 x))).eval (x 4) := by
  rw [theta5_specialize_coeff_identity, theta5Span4_polynomial x h0 h1 h2 h3]

theorem hasZeroSumSubspace_five_of_theta5_chain (x : Fin 5 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ theta5Span1 x) (h2 : x 2 ∉ theta5Span2 x)
    (h3 : x 3 ∉ theta5Span3 x) (h4 : x 4 ∉ theta5Span4 x)
    (htheta : MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0) :
    HasZeroSumSubspace K 5 := by
  have hzero := theta5_specialization_eq_span_polynomial x h0 h1 h2 h3
  rw [htheta] at hzero
  have heval : (rootProduct (underlyingFinset (theta5Span4 x))).eval (x 4) =
      ((rootProduct (underlyingFinset (theta5Span4 x))).coeff 8)^2 := by
    simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp hzero.symm).symm
  exact rankFour_extension_solution_gives_k5 (theta5Span4 x)
    (theta5Span4_rank x h0 h1 h2 h3) (x 4) h4 heval

/-- An independent zero of the explicit Θ₅ polynomial yields the original
    five-dimensional zero-sum conclusion over the arbitrary finite field. -/
theorem hasZeroSumSubspace_five_of_theta5_independent_zero (x : Fin 5 → K)
    (hli : LinearIndependent (ZMod 2) x)
    (htheta : MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0) :
    HasZeroSumSubspace K 5 := by
  have hin (i j : Fin 5) (hne : j ≠ i) :
      Submodule.span (ZMod 2) ({x j} : Set K) ≤
        Submodule.span (ZMod 2) (x '' {i}ᶜ) := by
    rw [Submodule.span_singleton_le_iff_mem]
    apply Submodule.subset_span
    exact ⟨j, by simpa using hne, rfl⟩
  have h0 : x 0 ≠ 0 := LinearIndependent.ne_zero 0 hli
  have h1 : x 1 ∉ theta5Span1 x := by
    intro hx
    apply hli.notMem_span 1
    exact hin 1 0 (by decide) hx
  have h2 : x 2 ∉ theta5Span2 x := by
    intro hx
    apply hli.notMem_span 2
    exact (sup_le (hin 2 0 (by decide)) (hin 2 1 (by decide))) hx
  have h3 : x 3 ∉ theta5Span3 x := by
    intro hx
    apply hli.notMem_span 3
    exact (sup_le (sup_le (hin 3 0 (by decide)) (hin 3 1 (by decide)))
      (hin 3 2 (by decide))) hx
  have h4 : x 4 ∉ theta5Span4 x := by
    intro hx
    apply hli.notMem_span 4
    exact (sup_le (sup_le (sup_le (hin 4 0 (by decide)) (hin 4 1 (by decide)))
      (hin 4 2 (by decide))) (hin 4 3 (by decide))) hx
  exact hasZeroSumSubspace_five_of_theta5_chain x h0 h1 h2 h3 h4 htheta

#print axioms theta5Span4_polynomial
#print axioms theta5Span4_rank
#print axioms theta5_specialization_eq_span_polynomial
#print axioms hasZeroSumSubspace_five_of_theta5_chain
#print axioms hasZeroSumSubspace_five_of_theta5_independent_zero

end Carlet
