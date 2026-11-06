import Carlet.FrobeniusCoefficients

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

def nextFrobeniusCoefficient (E : Submodule (ZMod 2) K) : K :=
  (rootProduct (underlyingFinset E)).coeff (2^(Module.finrank (ZMod 2) E-1))

omit [DecidableEq K] in
theorem subspacePolynomial_natDegree_pow (E : Submodule (ZMod 2) K) :
    (rootProduct (underlyingFinset E)).natDegree = 2^Module.finrank (ZMod 2) E := by
  rw [rootProduct_natDegree, underlyingFinset_card_pow]

theorem nextCoefficient_artinSchreier (H : Submodule (ZMod 2) K) (hH : (1 : K) ∈ H)
    (hdim : 2 ≤ Module.finrank (ZMod 2) H) :
    nextFrobeniusCoefficient H = 1 + nextFrobeniusCoefficient (H.map artinSchreier) := by
  let V := H.map artinSchreier
  have hdimV := artinSchreier_map_finrank H hH
  have hd : 0 < Module.finrank (ZMod 2) V := by dsimp [V]; omega
  have hindex : Module.finrank (ZMod 2) H-1 = Module.finrank (ZMod 2) V := by
    dsimp [V]
    omega
  have hc := coeff_comp_artinSchreier (rootProduct (underlyingFinset V))
    (subspacePolynomial_frobeniusSupported V) (Module.finrank (ZMod 2) V)
    (subspacePolynomial_natDegree_pow V).le hd
  have hlead : (rootProduct (underlyingFinset V)).coeff (2^Module.finrank (ZMod 2) V) = 1 := by
    rw [← subspacePolynomial_natDegree_pow V]
    exact (rootProduct_monic _).coeff_natDegree
  rw [artinSchreier_subspace_polynomial H hH, hlead] at hc
  change (rootProduct (underlyingFinset H)).coeff (2^(Module.finrank (ZMod 2) H-1)) = _
  rw [hindex, hc]
  exact add_comm _ _

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem artinSchreier_coefficient_fiber_iff (d : ℕ) (hd : 0 < d) (b : K)
    (H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H}) :
    (Module.finrank (ZMod 2) H.val = d+1 ∧ nextFrobeniusCoefficient H.val = b) ↔
      (Module.finrank (ZMod 2) (H.val.map artinSchreier) = d ∧
        nextFrobeniusCoefficient (H.val.map artinSchreier) = b+1) := by
  have hdim := artinSchreier_map_finrank H.val H.property
  constructor
  · rintro ⟨hr,ht⟩
    refine ⟨by omega, ?_⟩
    have hc := nextCoefficient_artinSchreier H.val H.property (by omega)
    rw [ht] at hc
    calc
      _ = 1+(1+nextFrobeniusCoefficient (H.val.map artinSchreier)) := by
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      _ = 1+b := congrArg (1+·) hc.symm
      _ = b+1 := add_comm _ _
  · rintro ⟨hr,ht⟩
    refine ⟨by omega, ?_⟩
    rw [nextCoefficient_artinSchreier H.val H.property (by omega), ht,
      add_left_comm, CharTwo.add_self_eq_zero, add_zero]

def coefficientFiberEquiv (d : ℕ) (hd : 0 < d) (b : K) :
    {H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H} //
      Module.finrank (ZMod 2) H.val = d+1 ∧ nextFrobeniusCoefficient H.val = b} ≃
    {V : {V : Submodule (ZMod 2) K // V ≤ LinearMap.ker (Algebra.trace (ZMod 2) K)} //
      Module.finrank (ZMod 2) V.val = d ∧ nextFrobeniusCoefficient V.val = b+1} :=
  artinSchreierSubspaceEquiv.subtypeEquiv (artinSchreier_coefficient_fiber_iff d hd b)

theorem coefficientFiber_card (d : ℕ) (hd : 0 < d) (b : K) :
    Nat.card {H : {H : Submodule (ZMod 2) K // (1 : K) ∈ H} //
      Module.finrank (ZMod 2) H.val = d+1 ∧ nextFrobeniusCoefficient H.val = b} =
    Nat.card {V : {V : Submodule (ZMod 2) K // V ≤ LinearMap.ker (Algebra.trace (ZMod 2) K)} //
      Module.finrank (ZMod 2) V.val = d ∧ nextFrobeniusCoefficient V.val = b+1} :=
  Nat.card_congr (coefficientFiberEquiv d hd b)

#print axioms nextCoefficient_artinSchreier
#print axioms coefficientFiberEquiv
#print axioms coefficientFiber_card

end Carlet
