import Carlet.ProbabilityNormalization
import Carlet.SubspaceCount

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

/-!
The flag identity is a natural-number equality.  This theorem is the
normalization bridge needed by `normalized_recursion_from_raw_counts`: it
turns that identity into the adjacent ratio of the actual containing-one
subspace fibers.  Nonemptiness of the lower fiber is stated explicitly here;
it is a separate existence fact, not an algebraic consequence of double
counting alone.
-/
omit [DecidableEq K] in
theorem adjacentOneFiber_real_ratio (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d ≤ n)
    (hA : Nat.card (dimensionFiberContainingOne (K := K) d) ≠ 0) :
    (Nat.card (dimensionFiberContainingOne (K := K) (d + 1)) : ℝ) /
        (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ) =
      ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) /
        ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) := by
  let A := Nat.card (dimensionFiberContainingOne (K := K) d)
  let B := Nat.card (dimensionFiberContainingOne (K := K) (d + 1))
  have hflag := adjacentOneFlags_double_count (K := K) n d hn
  have hpowNat : 2 ^ n = 2 ^ d * 2 ^ (n - d) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hdn]
  have hcardNat : Fintype.card K = 2 ^ n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    simpa only [ZMod.card, hn] using h
  have hq : (Fintype.card K : ℝ) = (2 ^ n : ℝ) := by exact_mod_cast hcardNat
  have hpow : (2 ^ n : ℝ) = (2 ^ d : ℝ) * (2 ^ (n - d) : ℝ) := by
    exact_mod_cast hpowNat
  have hnum : (Fintype.card K : ℝ) - (2 ^ d : ℝ) =
      (2 ^ d : ℝ) * ((2 ^ (n - d) : ℝ) - 1) := by
    rw [hq, hpow]
    ring
  have hflagReal : (A : ℝ) * ((2 ^ (n - d) : ℝ) - 1) =
      (B : ℝ) * ((2 ^ d : ℝ) - 1) := by
    dsimp [A, B]
    have h1 : (↑(2 ^ (n - d) - 1 : ℕ) : ℝ) =
        (2 ^ (n - d) : ℝ) - 1 := by
      have hpowPos : 0 < 2 ^ (n - d) := by positivity
      have hpos : 1 ≤ 2 ^ (n - d) := Nat.succ_le_iff.mpr hpowPos
      rw [Nat.cast_sub hpos, Nat.cast_pow]
      norm_num
    have h2 : (↑(2 ^ d - 1 : ℕ) : ℝ) =
        (2 ^ d : ℝ) - 1 := by
      have hpowPos : 0 < 2 ^ d := by positivity
      have hpos : 1 ≤ 2 ^ d := Nat.succ_le_iff.mpr hpowPos
      rw [Nat.cast_sub hpos, Nat.cast_pow]
      norm_num
    have hcast := congrArg (fun z : ℕ => (z : ℝ)) hflag
    rw [Nat.cast_mul, Nat.cast_mul, h1, h2] at hcast
    exact hcast
  have hAreal : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  have hpowPositive : (0 : ℝ) < (2 ^ d : ℝ) := by positivity
  have hdenPositive : (0 : ℝ) < (2 ^ d : ℝ) - 1 := by
    have hnat : 1 < 2 ^ d := Nat.one_lt_pow (Nat.ne_of_gt hd) (by decide)
    have hnatCast : (1 : ℝ) < (2 ^ d : ℝ) := by exact_mod_cast hnat
    linarith
  have hden : (2 ^ d : ℝ) - 1 ≠ 0 := ne_of_gt hdenPositive
  rw [hnum]
  field_simp [hAreal, hden, hpowPositive.ne']
  nlinarith [hflagReal]

set_option linter.style.haveILetI false in
omit [DecidableEq K] in
theorem dimensionFiberContainingOne_card_pos (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 1 ≤ d) (hdn : d ≤ n) :
    0 < Nat.card (dimensionFiberContainingOne (K := K) d) := by
  classical
  letI : Finite (Submodule (ZMod 2) K) :=
    Finite.of_injective (fun E : Submodule (ZMod 2) K => (E : Set K))
      SetLike.coe_injective
  have hbase : 0 < Nat.card (dimensionFiberContainingOne (K := K) 1) := by
    let E : Submodule (ZMod 2) K := (ZMod 2) ∙ (1 : K)
    have hdim : Module.finrank (ZMod 2) E = 1 := by
      simpa [E] using
        (finrank_span_singleton (K := ZMod 2) (V := K) (v := (1 : K)) one_ne_zero)
    have hone : (1 : K) ∈ E := by
      change (1 : K) ∈ (ZMod 2) ∙ (1 : K)
      exact Submodule.mem_span_singleton.mpr ⟨1, one_smul (ZMod 2) (1 : K)⟩
    let e : dimensionFiberContainingOne (K := K) 1 := ⟨E, hdim, hone⟩
    have hfinite : Finite (dimensionFiberContainingOne (K := K) 1) :=
      Finite.of_injective (fun F : dimensionFiberContainingOne (K := K) 1 => F.val)
        Subtype.val_injective
    exact Nat.card_pos_iff.mpr ⟨⟨e⟩, hfinite⟩
  have hwalk : ∀ j, 1 ≤ j → j ≤ d →
      0 < Nat.card (dimensionFiberContainingOne (K := K) j) := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
        intro hj hjd
        cases j with
        | zero => exact hbase
        | succ j =>
            have hprev : 0 < Nat.card (dimensionFiberContainingOne (K := K) (j + 1)) :=
              ih (by omega) (by omega)
            have hjlt : j + 1 < n := by omega
            have hflag := adjacentOneFlags_double_count (K := K) n (j + 1) hn
            have hleftFactor : 0 < 2 ^ (n - (j + 1)) - 1 := by
              have hpow : 1 < 2 ^ (n - (j + 1)) :=
                Nat.one_lt_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjlt)) (by decide)
              omega
            have hrightFactor : 0 < 2 ^ (j + 1) - 1 := by
              have hpow : 1 < 2 ^ (j + 1) :=
                Nat.one_lt_pow (by omega : j + 1 ≠ 0) (by decide)
              omega
            have hleft : 0 < Nat.card (dimensionFiberContainingOne (K := K) (j + 1)) *
                (2 ^ (n - (j + 1)) - 1) := Nat.mul_pos hprev hleftFactor
            rw [hflag] at hleft
            have hnext : 0 < Nat.card (dimensionFiberContainingOne (K := K) (j + 2)) := by
              by_contra hnot
              have hz : Nat.card (dimensionFiberContainingOne (K := K) (j + 2)) = 0 :=
                Nat.eq_zero_of_not_pos hnot
              simp [hz] at hleft
            simpa using hnext
  exact hwalk d hd le_rfl

omit [DecidableEq K] in
theorem adjacentOneFiber_real_ratio_of_bounds (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d ≤ n) :
    (Nat.card (dimensionFiberContainingOne (K := K) (d + 1)) : ℝ) /
        (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ) =
      ((Fintype.card K : ℝ) - (2 ^ d : ℝ)) /
        ((2 ^ d : ℝ) * ((2 ^ d : ℝ) - 1)) := by
  apply adjacentOneFiber_real_ratio n d hn hd hdn
  exact Nat.ne_of_gt (dimensionFiberContainingOne_card_pos n d hn (by omega) hdn)

#print axioms adjacentOneFiber_real_ratio
#print axioms dimensionFiberContainingOne_card_pos
#print axioms adjacentOneFiber_real_ratio_of_bounds

end Carlet
