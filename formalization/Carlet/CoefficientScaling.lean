import Carlet.SubspaceScaling

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

def coefficientFiber (k : ℕ) (b : K) :=
  {E : Submodule (ZMod 2) K // Module.finrank (ZMod 2) E = k ∧
    nextFrobeniusCoefficient E = b}

def coefficientFiber_equiv_of_nonzero (k : ℕ) (hk : 0 < k) (b c : K)
    (hb : b ≠ 0) (hc : c ≠ 0) : coefficientFiber k b ≃ coefficientFiber k c := by
  let hroot := pow_two_surjective (K := K) (k-1) (c / b)
  let z := Classical.choose hroot
  have hz : z^(2^(k-1)) = c / b := Classical.choose_spec hroot
  have hz0 : z ≠ 0 := by
    intro hz0
    have hexp : 0 < 2^(k-1) := Nat.pow_pos (by decide)
    rw [hz0, zero_pow (Nat.ne_of_gt hexp)] at hz
    exact hc ((div_eq_zero_iff.mp hz.symm).resolve_right hb)
  let a : Kˣ := Units.mk0 z hz0
  have hpower : (a : K)^(2^(k-1)) = c / b := hz
  have hfac : (a : K)^(2^(k-1)) ≠ 0 := pow_ne_zero _ (Units.ne_zero a)
  have hmul : (a : K)^(2^(k-1)) * b = c := by
    rw [hpower]
    field_simp
  have hτ (E : Submodule (ZMod 2) K) (hr : Module.finrank (ZMod 2) E = k) :
      nextFrobeniusCoefficient (scalarSubspace E a) = c ↔
        nextFrobeniusCoefficient E = b := by
    rw [nextCoefficient_scalarSubspace E a (by omega), hr]
    constructor
    · intro he
      exact mul_left_cancel₀ hfac (he.trans hmul.symm)
    · intro he
      rw [he, hmul]
  exact (scalarSubspaceEquiv a).subtypeEquiv (fun E => by
    change (Module.finrank (ZMod 2) E = k ∧ nextFrobeniusCoefficient E = b) ↔
      (Module.finrank (ZMod 2) (scalarSubspace E a) = k ∧
        nextFrobeniusCoefficient (scalarSubspace E a) = c)
    rw [scalarSubspace_finrank E a]
    constructor
    · rintro ⟨hr, ht⟩
      exact ⟨hr, (hτ E hr).2 ht⟩
    · rintro ⟨hr, ht⟩
      exact ⟨hr, (hτ E hr).1 ht⟩)

omit [DecidableEq K] in
theorem coefficientFiber_card_eq_of_nonzero (k : ℕ) (hk : 0 < k) (b c : K)
    (hb : b ≠ 0) (hc : c ≠ 0) : Nat.card (coefficientFiber k b) = Nat.card (coefficientFiber k c) :=
  Nat.card_congr (coefficientFiber_equiv_of_nonzero k hk b c hb hc)

#print axioms coefficientFiber_equiv_of_nonzero
#print axioms coefficientFiber_card_eq_of_nonzero

end Carlet
