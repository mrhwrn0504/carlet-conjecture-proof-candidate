import Carlet.K4ThetaSpecializationProbe
import Carlet.K4ThetaCoefficientBridgeProbe

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open Polynomial
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

def k4Span1 (x : Fin 4 → K) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) ({x 0} : Set K)
def k4Span2 (x : Fin 4 → K) : Submodule (ZMod 2) K :=
  k4Span1 x ⊔ Submodule.span (ZMod 2) ({x 1} : Set K)
def k4Span3 (x : Fin 4 → K) : Submodule (ZMod 2) K :=
  k4Span2 x ⊔ Submodule.span (ZMod 2) ({x 2} : Set K)
def k4Span4 (x : Fin 4 → K) : Submodule (ZMod 2) K :=
  k4Span3 x ⊔ Submodule.span (ZMod 2) ({x 3} : Set K)

theorem k4Span1_polynomial (x : Fin 4 → K) (h0 : x 0 ≠ 0) :
    rootProduct (underlyingFinset (k4Span1 x)) = k4SpecialP1 x := by
  have hb : underlyingFinset (⊥ : Submodule (ZMod 2) K) = {0} := by
    ext y
    simp
  have hp : rootProduct (underlyingFinset (⊥ : Submodule (ZMod 2) K)) =
      (Polynomial.X : Polynomial K) := by simp [hb, rootProduct]
  have hnot : x 0 ∉ (⊥ : Submodule (ZMod 2) K) := by simpa using h0
  have he := subspacePolynomial_extension (⊥ : Submodule (ZMod 2) K) (x 0) hnot
  rw [bot_sup_eq, hp] at he
  simpa [k4Span1, k4SpecialP1_eq] using he

theorem k4Span4_polynomial (x : Fin 4 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ k4Span1 x) (h2 : x 2 ∉ k4Span2 x)
    (h3 : x 3 ∉ k4Span3 x) :
    rootProduct (underlyingFinset (k4Span4 x)) = k4SpecialPolynomial x := by
  have hp1 := k4Span1_polynomial x h0
  have hp2 : rootProduct (underlyingFinset (k4Span2 x)) = k4SpecialP2 x := by
    rw [k4Span2, subspacePolynomial_extension _ _ h1, hp1, k4SpecialP2_eq]
  have hp3 : rootProduct (underlyingFinset (k4Span3 x)) = k4SpecialP3 x := by
    rw [k4Span3, subspacePolynomial_extension _ _ h2, hp2, k4SpecialP3_eq]
  rw [k4Span4, subspacePolynomial_extension _ _ h3, hp3, k4SpecialPolynomial_eq]

theorem k4Span4_coeff_eight (x : Fin 4 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ k4Span1 x) (h2 : x 2 ∉ k4Span2 x)
    (h3 : x 3 ∉ k4Span3 x) :
    (rootProduct (underlyingFinset (k4Span4 x))).coeff 8 =
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) := by
  rw [k4Span4_polynomial x h0 h1 h2 h3, k4SpecialPolynomial_coeff_eight]

omit [DecidableEq K] in
theorem k4Span4_rank (x : Fin 4 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ k4Span1 x) (h2 : x 2 ∉ k4Span2 x)
    (h3 : x 3 ∉ k4Span3 x) :
    Module.finrank (ZMod 2) (k4Span4 x) = 4 := by
  have hr1 : Module.finrank (ZMod 2) (k4Span1 x) = 1 :=
    finrank_span_singleton (K := ZMod 2) (V := K) h0
  rw [k4Span4, extension_finrank _ _ h3, k4Span3,
    extension_finrank _ _ h2, k4Span2, extension_finrank _ _ h1, hr1]

theorem hasZeroSumSubspace_four_of_theta4_chain (x : Fin 4 → K) (h0 : x 0 ≠ 0)
    (h1 : x 1 ∉ k4Span1 x) (h2 : x 2 ∉ k4Span2 x)
    (h3 : x 3 ∉ k4Span3 x)
    (htheta : MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0) :
    HasZeroSumSubspace K 4 := by
  have hr := k4Span4_rank x h0 h1 h2 h3
  have hc : (rootProduct (underlyingFinset (k4Span4 x))).coeff 8 = 0 := by
    rw [k4Span4_coeff_eight x h0 h1 h2 h3, htheta]
  exact ⟨dualImageEquiv (k4Span4 x), by rw [dualImage_finrank, hr],
    (zeroSum_dualImage_iff_coeff8 (k4Span4 x) hr).mpr hc⟩

#print axioms k4Span4_rank
#print axioms hasZeroSumSubspace_four_of_theta4_chain
#print axioms k4Span1_polynomial
#print axioms k4Span4_polynomial
#print axioms k4Span4_coeff_eight
end Carlet
