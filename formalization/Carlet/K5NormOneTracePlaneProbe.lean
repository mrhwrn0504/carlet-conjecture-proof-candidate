import Carlet.K5NormOneTraceCountProbe
import Carlet.K5RankThreeSeedProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type} [Field K] [Fintype K]
  [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
local instance (E : Submodule (ZMod 2) K) : Fintype E := Fintype.ofFinite E

def k5NormOneTracePlane (U : Submodule (ZMod 2) K) (c : K) :
    Submodule (ZMod 2) K :=
  traceOrthogonal (LinearMap.range (k4ScaledSubspacePolynomialMap U c⁻¹))

theorem k5NormOneTracePlane_finrank (U : Submodule (ZMod 2) K) (c : K)
    (hU : Module.finrank (ZMod 2) U = 3) (hc : c ≠ 0) :
    Module.finrank (ZMod 2) (k5NormOneTracePlane U c) = 3 := by
  let g := k4ScaledSubspacePolynomialMap U c⁻¹
  have hker : LinearMap.ker g = U := by
    simpa [g] using k4ScaledSubspacePolynomialMap_ker U c⁻¹ (inv_ne_zero hc)
  have hrange := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, hU] at hrange
  change Module.finrank (ZMod 2) (traceOrthogonal (LinearMap.range g)) = 3
  rw [traceOrthogonal_finrank]
  omega

theorem k5NormOneTracePlane_card (U : Submodule (ZMod 2) K) (c : K)
    (hU : Module.finrank (ZMod 2) U = 3) (hc : c ≠ 0) :
    Fintype.card (k5NormOneTracePlane U c) = 8 := by
  have hdim := k5NormOneTracePlane_finrank U c hU hc
  have hpow := Module.card_eq_pow_finrank (K := ZMod 2) (V := k5NormOneTracePlane U c)
  simpa [Nat.card_eq_fintype_card, ZMod.card, hdim] using hpow

theorem k5NormOneTracePlane_exists_nondegenerate (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K = n)
    (U : Submodule (ZMod 2) K) (c : K)
    (hU : Module.finrank (ZMod 2) U = 3) (hc : c ≠ 0)
    (hq : 65536 ≤ Fintype.card K) :
    ∃ p : k4NormOnePairs (K := K),
      k4GeneralTraceGood (k5NormOneTracePlane U c) p ∧
      p.val.1 ≠ 0 ∧ p.val.1 ≠ 1 := by
  classical
  let Good := {p : k4NormOnePairs (K := K) //
    k4GeneralTraceGood (k5NormOneTracePlane U c) p}
  have hcount : 3 < Fintype.card Good := by
    simpa [Good] using k5GeneralTraceGood_card_gt_three n hn hfinrank
      (k5NormOneTracePlane U c) (k5NormOneTracePlane_card U c hU hc) hq
  have hexists : ¬ ∀ p : Good, p.val.val.1 = 0 ∨ p.val.val.1 = 1 := by
    intro hall
    let f : Good → k4NormOneBadFirstPairs (K := K) := fun p => ⟨p.val, hall p⟩
    have hinj : Function.Injective f := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg (fun r : k4NormOneBadFirstPairs (K := K) => r.val) hpq
    have hle := Fintype.card_le_of_injective f hinj
    have hle' : Fintype.card Good ≤ 3 := by
      calc
        Fintype.card Good ≤ Fintype.card (k4NormOneBadFirstPairs (K := K)) := hle
        _ ≤ 3 := k4NormOneBadFirstPairs_card_le_three
    omega
  obtain ⟨p, hp⟩ := not_forall.mp hexists
  let q : k4NormOnePairs (K := K) := p.val
  have hp0 : q.val.1 ≠ 0 := by
    intro h
    apply hp
    exact Or.inl (by simpa [q] using h)
  have hp1 : q.val.1 ≠ 1 := by
    intro h
    apply hp
    exact Or.inr (by simpa [q] using h)
  exact ⟨q, p.property, hp0, hp1⟩

theorem k5NormOneTracePlane_preimage (U : Submodule (ZMod 2) K) (c a : K)
    (hc : c ≠ 0)
    (htrace : ∀ w ∈ k5NormOneTracePlane U c,
      Algebra.trace (ZMod 2) K (w * a) = 0) :
    ∃ x : K, (rootProduct (underlyingFinset U)).eval x = c * a := by
  have horth : a ∈ traceOrthogonal (k5NormOneTracePlane U c) := by
    change a ∈ (Algebra.traceForm (ZMod 2) K).orthogonal (k5NormOneTracePlane U c)
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    simpa [Algebra.traceForm, mul_comm] using htrace w hw
  have hdouble : traceOrthogonal (k5NormOneTracePlane U c) =
      LinearMap.range (k4ScaledSubspacePolynomialMap U c⁻¹) := by
    dsimp [k5NormOneTracePlane]
    exact traceOrthogonal_involutive _
  rw [hdouble] at horth
  obtain ⟨x, hx⟩ := horth
  have hx' : c⁻¹ * (rootProduct (underlyingFinset U)).eval x = a := by
    simpa [k4ScaledSubspacePolynomialMap, k4ScalarMulMap,
      subspacePolynomialMap] using hx
  refine ⟨x, ?_⟩
  calc
    (rootProduct (underlyingFinset U)).eval x =
        c * (c⁻¹ * (rootProduct (underlyingFinset U)).eval x) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = c * a := by rw [hx']

#print axioms k5NormOneTracePlane_finrank
#print axioms k5NormOneTracePlane_exists_nondegenerate
#print axioms k5NormOneTracePlane_preimage
end Carlet
