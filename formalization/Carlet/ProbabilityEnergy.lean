import Carlet.ConcreteProbabilityRecursion
import Carlet.DualSubspacePolynomial
import Carlet.TwoStepEnergy

noncomputable section

open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

def centeredContainingOneProbability (d : ℕ) (b : K) : ℝ :=
  containingOneCoefficientProbability (K := K) d b - 1 / (Fintype.card K : ℝ)

def centeredPairEnergyFactor (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r,
    (4 * (2 ^ (2 * j + 1) : ℝ) ^ 2 / (Fintype.card K : ℝ))

omit [DecidableEq K] in
theorem centeredContainingOneProbability_sum_zero (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 0 < d) (hdn : d ≤ n) :
    (∑ b : K, centeredContainingOneProbability (K := K) d b) = 0 := by
  classical
  have hprob := containingOne_probability_sum (K := K) n d hn hd hdn
  have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [centeredContainingOneProbability, Finset.sum_sub_distrib, hprob]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  field_simp [hq]
  ring

theorem centeredContainingOneProbability_transfer (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d < n)
    (hs : (Fintype.card K : ℝ) - (2 ^ d : ℝ) ≠ 0) (b : K) :
    Transfer.transfer (traceCharacter (K := K)) (2 ^ d : ℝ)
        (centeredContainingOneProbability (K := K) d) b =
      centeredContainingOneProbability (K := K) (d + 1) b := by
  classical
  change Transfer.transfer (traceCharacter (K := K)) (2 ^ d : ℝ)
      (fun x => containingOneCoefficientProbability (K := K) d x -
        (fun _ : K => 1 / (Fintype.card K : ℝ)) x) b = _
  rw [Transfer.transfer_sub,
    containingOne_probability_transfer (K := K) n d hn hd hdn b,
    Transfer.transfer_constant (traceCharacter (K := K))
      (traceCharacter_ne_zero (K := K)) (2 ^ d : ℝ)
      (1 / (Fintype.card K : ℝ)) hs b]
  rfl

set_option linter.style.haveILetI false in
theorem centeredContainingOneProbability_twoStep_energy (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d + 2 ≤ n)
    (hq : 32 * (2 ^ d : ℝ) ^ 2 ≤ (Fintype.card K : ℝ)) :
    Transfer.energy (centeredContainingOneProbability (K := K) (d + 2)) ≤
      (4 * (2 ^ d : ℝ) ^ 2 / (Fintype.card K : ℝ)) *
        Transfer.energy (centeredContainingOneProbability (K := K) d) := by
  classical
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  let s : ℝ := (2 ^ d : ℝ)
  have hs : 2 ≤ s := by
    dsimp [s]
    have hpow : 2 ≤ 2 ^ d := by
      have h := Nat.one_lt_pow (Nat.ne_of_gt hd) (by decide : 1 < 2)
      omega
    exact_mod_cast hpow
  have hden1 : (Fintype.card K : ℝ) - s ≠ 0 := by
    apply ne_of_gt
    nlinarith [hq]
  have hden2 : (Fintype.card K : ℝ) - 2 * s ≠ 0 := by
    apply ne_of_gt
    nlinarith [hq]
  have hzero := centeredContainingOneProbability_sum_zero (K := K) n d hn hd (by omega)
  have hcontract := Transfer.twoStep_energy_contraction_card
    (traceCharacter (K := K)) (traceCharacter_ne_zero (K := K)) s hs
    (by simpa [s] using hq)
    (centeredContainingOneProbability (K := K) d) hzero
  have hfirst : Transfer.transfer (traceCharacter (K := K)) s
      (centeredContainingOneProbability (K := K) d) =
        centeredContainingOneProbability (K := K) (d + 1) := by
    funext b
    exact centeredContainingOneProbability_transfer n d hn hd (by omega) hden1 b
  have hparam : 2 * s = (2 ^ (d + 1) : ℝ) := by
    dsimp [s]
    rw [pow_succ]
    ring
  have hden2' : (Fintype.card K : ℝ) - (2 ^ (d + 1) : ℝ) ≠ 0 := by
    rw [← hparam]
    exact hden2
  have hsecond : Transfer.transfer (traceCharacter (K := K)) (2 * s)
      (centeredContainingOneProbability (K := K) (d + 1)) =
        centeredContainingOneProbability (K := K) (d + 2) := by
    rw [hparam]
    funext b
    exact centeredContainingOneProbability_transfer n (d + 1) hn (by omega)
      (by omega) hden2' b
  change Transfer.energy (Transfer.transfer (traceCharacter (K := K)) (2 * s)
      (Transfer.transfer (traceCharacter (K := K)) s
        (centeredContainingOneProbability (K := K) d)) ) ≤ _ at hcontract
  rw [hfirst, hsecond] at hcontract
  simpa [s] using hcontract

set_option linter.style.haveILetI false in
theorem centeredContainingOneProbability_oneStep_energy (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d < n)
    (hsq : (2 ^ d : ℝ) ^ 2 ≤ (Fintype.card K : ℝ))
    (hstrict : (2 ^ d : ℝ) < (Fintype.card K : ℝ)) :
    Transfer.energy (centeredContainingOneProbability (K := K) (d + 1)) ≤
      Transfer.energy (centeredContainingOneProbability (K := K) d) := by
  classical
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  let s : ℝ := (2 ^ d : ℝ)
  let t : ℝ := Real.sqrt (Fintype.card K : ℝ)
  have hs : 1 ≤ s := by
    dsimp [s]
    have hpow : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
    exact_mod_cast hpow
  have ht : 0 < t := by
    dsimp [t]
    exact Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have htq : t ^ 2 = (Fintype.card K : ℝ) := by
    dsimp [t]
    rw [Real.sq_sqrt]
    exact le_of_lt (by exact_mod_cast Fintype.card_pos)
  have hden : (Fintype.card K : ℝ) - (2 ^ d : ℝ) ≠ 0 :=
    (sub_pos.mpr hstrict).ne'
  have hzero := centeredContainingOneProbability_sum_zero (K := K) n d hn hd (by omega)
  have hstep := Transfer.oneStep_energy_nonexpansive
    (traceCharacter (K := K)) (traceCharacter_ne_zero (K := K)) s t hs
    (by simpa [s] using hsq) (by simpa [s] using hstrict) ht htq
    (centeredContainingOneProbability (K := K) d) hzero
  have hrec : Transfer.transfer (traceCharacter (K := K)) s
      (centeredContainingOneProbability (K := K) d) =
        centeredContainingOneProbability (K := K) (d + 1) := by
    funext b
    exact centeredContainingOneProbability_transfer n d hn hd hdn
      hden b
  change Transfer.energy (Transfer.transfer (traceCharacter (K := K)) s
    (centeredContainingOneProbability (K := K) d)) ≤ _ at hstep
  rw [hrec] at hstep
  simpa [s] using hstep

theorem centeredContainingOneProbability_odd_energy_bound (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 2 * r + 1 ≤ n)
    (hq : ∀ j, j < r →
      32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ)) :
    Transfer.energy (centeredContainingOneProbability (K := K) (2 * r + 1)) ≤
      centeredPairEnergyFactor (K := K) r *
        Transfer.energy (centeredContainingOneProbability (K := K) 1) := by
  classical
  induction r generalizing n with
  | zero =>
      simp [centeredPairEnergyFactor]
  | succ r ih =>
      have hIH := ih n hn (by omega) (fun j hj => hq j (by omega))
      have hpair := centeredContainingOneProbability_twoStep_energy
        (K := K) n (2 * r + 1) hn (by omega) (by omega) (hq r (by omega))
      have hindex : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
      rw [hindex]
      let c : ℝ :=
        4 * (2 ^ (2 * r + 1) : ℝ) ^ 2 / (Fintype.card K : ℝ)
      have hc : 0 ≤ c := by dsimp [c]; positivity
      calc
        Transfer.energy (centeredContainingOneProbability (K := K) ((2 * r + 1) + 2))
            ≤ c * Transfer.energy
                (centeredContainingOneProbability (K := K) (2 * r + 1)) := by
              simpa [c] using hpair
        _ ≤ c * (centeredPairEnergyFactor (K := K) r *
              Transfer.energy (centeredContainingOneProbability (K := K) 1)) :=
            mul_le_mul_of_nonneg_left hIH hc
        _ = centeredPairEnergyFactor (K := K) (r + 1) *
              Transfer.energy (centeredContainingOneProbability (K := K) 1) := by
            have hfactor : c * centeredPairEnergyFactor (K := K) r =
                centeredPairEnergyFactor (K := K) (r + 1) := by
              dsimp [c, centeredPairEnergyFactor]
              rw [Finset.prod_range_succ]
              ring
            calc
              _ = (c * centeredPairEnergyFactor (K := K) r) *
                  Transfer.energy (centeredContainingOneProbability (K := K) 1) := by ring
              _ = _ := by rw [hfactor]

omit [Algebra (ZMod 2) K] [DecidableEq K] in
theorem centeredPairEnergyFactor_closed (r : ℕ) :
    centeredPairEnergyFactor (K := K) r =
      (2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r := by
  classical
  induction r with
  | zero => simp [centeredPairEnergyFactor]
  | succ r ih =>
      have hP : centeredPairEnergyFactor (K := K) (r + 1) =
          centeredPairEnergyFactor (K := K) r *
            (4 * (2 ^ (2 * r + 1) : ℝ) ^ 2 / (Fintype.card K : ℝ)) := by
        dsimp [centeredPairEnergyFactor]
        rw [Finset.prod_range_succ]
      rw [hP, ih]
      have hexp : 2 * (r + 1) ^ 2 + 2 * (r + 1) =
          (2 * r ^ 2 + 2 * r) + (2 * (2 * r + 1) + 2) := by ring
      have hpair : 4 * (2 ^ (2 * r + 1) : ℝ) ^ 2 =
          (2 : ℝ) ^ (2 * (2 * r + 1) + 2) := by
        calc
          _ = (2 : ℝ) ^ 2 * (2 ^ (2 * r + 1) : ℝ) ^ 2 := by norm_num
          _ = (2 : ℝ) ^ (2 + (2 * r + 1) * 2) := by
            rw [← pow_mul, ← pow_add]
          _ = _ := by congr 1; omega
      have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [pow_succ]
      rw [hpair]
      field_simp [hq]
      rw [← pow_add, hexp]
      ring

theorem centeredContainingOneProbability_initial_energy (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hnpos : 1 ≤ n) :
    Transfer.energy (centeredContainingOneProbability (K := K) 1) =
      1 - 1 / (Fintype.card K : ℝ) := by
  classical
  have hfun : centeredContainingOneProbability (K := K) 1 =
      Transfer.centeredDelta 1 := by
    funext b
    simp [centeredContainingOneProbability, containingOne_probability_one_dim
      (K := K) n hn hnpos, Transfer.centeredDelta]
  rw [hfun]
  change (∑ x : K, Transfer.centeredDelta 1 x ^ 2) = _
  rw [Transfer.centeredDelta_sq_sum]

theorem centeredContainingOneProbability_odd_energy_explicit (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 2 * r + 1 ≤ n)
    (hq : ∀ j, j < r →
      32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ))
    (hnpos : 1 ≤ n) :
    Transfer.energy (centeredContainingOneProbability (K := K) (2 * r + 1)) ≤
      ((2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r) *
        (1 - 1 / (Fintype.card K : ℝ)) := by
  calc
    _ ≤ centeredPairEnergyFactor (K := K) r *
        Transfer.energy (centeredContainingOneProbability (K := K) 1) :=
      centeredContainingOneProbability_odd_energy_bound (K := K) n r hn hr hq
    _ = _ := by
      rw [centeredPairEnergyFactor_closed,
        centeredContainingOneProbability_initial_energy (K := K) n hn hnpos]

theorem centeredContainingOneProbability_even_energy_explicit (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 2 * r + 2 ≤ n)
    (hq : ∀ j, j < r →
      32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ))
    (hsq : (2 ^ (2 * r + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ))
    (hstrict : (2 ^ (2 * r + 1) : ℝ) < (Fintype.card K : ℝ)) :
    Transfer.energy (centeredContainingOneProbability (K := K) (2 * r + 2)) ≤
      ((2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r) *
        (1 - 1 / (Fintype.card K : ℝ)) := by
  have hodd := centeredContainingOneProbability_odd_energy_explicit
    (K := K) n r hn (by omega) hq (by omega)
  have hone := centeredContainingOneProbability_oneStep_energy
    (K := K) n (2 * r + 1) hn (by omega) (by omega) hsq hstrict
  exact hone.trans hodd

theorem odd_energy_exponent_lt (r n : ℕ) (hr : 5 ≤ r) (hn : 4 * r + 3 ≤ n) :
    2 * r ^ 2 + 2 * r < n * (r - 2) := by
  have hprod := Nat.mul_le_mul_right (r - 2) hn
  have hrsub : 2 ≤ r := by omega
  have hpoly : 2 * r ^ 2 + 2 * r < (4 * r + 3) * (r - 2) := by
    have hrR : (5 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hpolyR : 2 * (r : ℝ) ^ 2 + 2 * (r : ℝ) <
        (4 * (r : ℝ) + 3) * ((r : ℝ) - 2) := by
      nlinarith [sq_nonneg ((r : ℝ) - 5)]
    exact_mod_cast hpolyR
  omega

theorem even_energy_exponent_lt (r n : ℕ) (hr : 4 ≤ r) (hn : 4 * r + 5 ≤ n) :
    2 * r ^ 2 + 2 * r < n * (r - 2) := by
  have hprod := Nat.mul_le_mul_right (r - 2) hn
  have hrsub : 2 ≤ r := by omega
  have hpoly : 2 * r ^ 2 + 2 * r < (4 * r + 5) * (r - 2) := by
    have hrR : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hpolyR : 2 * (r : ℝ) ^ 2 + 2 * (r : ℝ) <
        (4 * (r : ℝ) + 5) * ((r : ℝ) - 2) := by
      nlinarith [sq_nonneg ((r : ℝ) - 4)]
    exact_mod_cast hpolyR
  omega

theorem energyFactor_lt_inv_sq_of_exponent (n r : ℕ) (hr : 2 ≤ r)
    (hexp : 2 * r ^ 2 + 2 * r < n * (r - 2)) :
    ((2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (2 ^ n : ℝ) ^ r) <
      1 / (2 ^ n : ℝ) ^ 2 := by
  have hexp' : 2 * r ^ 2 + 2 * r + n * 2 < n * r := by
    have hmul : n * (r - 2) + n * 2 = n * r := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hr]
    omega
  have hpowNat :
      2 ^ (2 * r ^ 2 + 2 * r + n * 2) < 2 ^ (n * r) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hexp'
  have hpowReal :
      (2 ^ (2 * r ^ 2 + 2 * r + n * 2) : ℝ) < (2 ^ (n * r) : ℝ) := by
    exact_mod_cast hpowNat
  rw [← pow_mul, ← pow_mul]
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (2 ^ (n * r) : ℝ))
    (by positivity : (0 : ℝ) < (2 ^ (n * 2) : ℝ))]
  rw [← pow_add]
  simpa using hpowReal

omit [DecidableEq K] in
theorem field_card_eq_pow_finrank_local (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) : Fintype.card K = 2 ^ n := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  simpa only [ZMod.card, hn] using h

omit [DecidableEq K] in
theorem pairEnergyCondition_of_dimension_bound (n j : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hbound : 4 * j + 7 ≤ n) :
    32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ) := by
  have hcard := field_card_eq_pow_finrank_local (K := K) n hn
  have hpower : 32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 =
      (2 ^ (4 * j + 7) : ℝ) := by
    calc
      _ = (2 : ℝ) ^ 5 * (2 ^ (2 * j + 1) : ℝ) ^ 2 := by norm_num
      _ = (2 : ℝ) ^ 5 * (2 : ℝ) ^ ((2 * j + 1) * 2) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (5 + (2 * j + 1) * 2) := by rw [← pow_add]
      _ = _ := by congr 1; omega
  have hnat : 2 ^ (4 * j + 7) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbound
  calc
    _ = (2 ^ (4 * j + 7) : ℝ) := hpower
    _ ≤ (2 ^ n : ℝ) := by exact_mod_cast hnat
    _ = (Fintype.card K : ℝ) := by exact_mod_cast hcard.symm

theorem centeredContainingOneProbability_odd_energy_lt_inv_sq (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 5 ≤ r) (hnbound : 4 * r + 3 ≤ n) :
    Transfer.energy (centeredContainingOneProbability (K := K) (2 * r + 1)) <
      1 / (Fintype.card K : ℝ) ^ 2 := by
  have hpair : ∀ j, j < r →
      32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ) := by
    intro j hj
    exact pairEnergyCondition_of_dimension_bound (K := K) n j hn (by omega)
  have henergy := centeredContainingOneProbability_odd_energy_explicit
    (K := K) n r hn (by omega) hpair (by omega)
  have hcard := field_card_eq_pow_finrank_local (K := K) n hn
  have hcardR : (Fintype.card K : ℝ) = (2 ^ n : ℝ) := by exact_mod_cast hcard
  have hexp := odd_energy_exponent_lt r n hr hnbound
  have hfactor := energyFactor_lt_inv_sq_of_exponent n r (by omega) hexp
  have hfactorNonneg : 0 ≤
      (2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r := by
    positivity
  have hmult : 1 - 1 / (Fintype.card K : ℝ) ≤ 1 := by
    have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    have hrecip : 0 ≤ 1 / (Fintype.card K : ℝ) := by positivity
    linarith
  calc
    _ ≤ ((2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r) *
        (1 - 1 / (Fintype.card K : ℝ)) := henergy
    _ ≤ (2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmult hfactorNonneg
    _ < 1 / (Fintype.card K : ℝ) ^ 2 := by simpa [hcardR] using hfactor

theorem centeredContainingOneProbability_even_energy_lt_inv_sq (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 4 ≤ r) (hnbound : 4 * r + 5 ≤ n) :
    Transfer.energy (centeredContainingOneProbability (K := K) (2 * r + 2)) <
      1 / (Fintype.card K : ℝ) ^ 2 := by
  have hpair : ∀ j, j < r →
      32 * (2 ^ (2 * j + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ) := by
    intro j hj
    exact pairEnergyCondition_of_dimension_bound (K := K) n j hn (by omega)
  have hcard := field_card_eq_pow_finrank_local (K := K) n hn
  have hsquareNat : 2 ^ (2 * (2 * r + 1)) ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  have hsquare : (2 ^ (2 * r + 1) : ℝ) ^ 2 ≤ (Fintype.card K : ℝ) := by
    have hpow : (2 ^ (2 * r + 1) : ℝ) ^ 2 =
        (2 ^ (2 * (2 * r + 1)) : ℝ) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow]
    exact_mod_cast (hsquareNat.trans_eq hcard.symm)
  have hstrictNat : 2 ^ (2 * r + 1) < 2 ^ n :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  have hstrict : (2 ^ (2 * r + 1) : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast (hstrictNat.trans_eq hcard.symm)
  have henergy := centeredContainingOneProbability_even_energy_explicit
    (K := K) n r hn (by omega) hpair hsquare hstrict
  have hcardR : (Fintype.card K : ℝ) = (2 ^ n : ℝ) := by exact_mod_cast hcard
  have hexp := even_energy_exponent_lt r n hr hnbound
  have hfactor := energyFactor_lt_inv_sq_of_exponent n r (by omega) hexp
  have hfactorNonneg : 0 ≤
      (2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r := by
    positivity
  have hmult : 1 - 1 / (Fintype.card K : ℝ) ≤ 1 := by
    have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    have hrecip : 0 ≤ 1 / (Fintype.card K : ℝ) := by positivity
    linarith
  calc
    _ ≤ ((2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r) *
        (1 - 1 / (Fintype.card K : ℝ)) := henergy
    _ ≤ (2 ^ (2 * r ^ 2 + 2 * r) : ℝ) / (Fintype.card K : ℝ) ^ r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmult hfactorNonneg
    _ < 1 / (Fintype.card K : ℝ) ^ 2 := by simpa [hcardR] using hfactor

theorem centered_energy_lt_inv_sq_implies_probability_pos (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hd : 0 < d) (hdn : d ≤ n)
    (henergy : Transfer.energy (centeredContainingOneProbability (K := K) d) <
      1 / (Fintype.card K : ℝ) ^ 2) :
    0 < containingOneCoefficientProbability (K := K) d 0 := by
  classical
  let p := containingOneCoefficientProbability (K := K) d 0
  have hdenNat := dimensionFiberContainingOne_card_pos n d hn (by omega) hdn
  have hden : 0 < (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ) := by
    exact_mod_cast hdenNat
  have hpnonneg : 0 ≤ p := by
    dsimp [p, containingOneCoefficientProbability]
    exact div_nonneg (Nat.cast_nonneg _) hden.le
  by_contra hpnot
  have hpzero : p = 0 := le_antisymm (le_of_not_gt hpnot) hpnonneg
  have hcenter : centeredContainingOneProbability (K := K) d 0 =
      -1 / (Fintype.card K : ℝ) := by
    change p - 1 / (Fintype.card K : ℝ) = -1 / (Fintype.card K : ℝ)
    rw [hpzero]
    ring
  let f := centeredContainingOneProbability (K := K) d
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset K)
    (fun x => f x ^ 2) (Finset.mem_univ 0)
  have htail : 0 ≤ ∑ x ∈ (Finset.univ : Finset K).erase 0, f x ^ 2 :=
    Finset.sum_nonneg (fun x hx => sq_nonneg (f x))
  have henergyLower : 1 / (Fintype.card K : ℝ) ^ 2 ≤ Transfer.energy f := by
    have hsplit' :
        (∑ x ∈ (Finset.univ : Finset K).erase 0, f x ^ 2) + f 0 ^ 2 =
          Transfer.energy f := by
      change (∑ x ∈ (Finset.univ : Finset K).erase 0, f x ^ 2) + f 0 ^ 2 =
        (∑ x : K, f x ^ 2)
      exact hsplit
    have hcoord : f 0 ^ 2 ≤ Transfer.energy f := by linarith
    have hcenter' : f 0 = -1 / (Fintype.card K : ℝ) := hcenter
    rw [hcenter'] at hcoord
    have hsq : (-1 / (Fintype.card K : ℝ)) ^ 2 =
        1 / (Fintype.card K : ℝ) ^ 2 := by ring
    rw [hsq] at hcoord
    exact hcoord
  linarith

theorem containingOne_probability_zero_pos_odd_high (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 5 ≤ r) (hnbound : 4 * r + 3 ≤ n) :
    0 < containingOneCoefficientProbability (K := K) (2 * r + 1) 0 := by
  apply centered_energy_lt_inv_sq_implies_probability_pos n (2 * r + 1) hn
    (by omega) (by omega)
  exact centeredContainingOneProbability_odd_energy_lt_inv_sq n r hn hr hnbound

theorem containingOne_probability_zero_pos_even_high (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 4 ≤ r) (hnbound : 4 * r + 5 ≤ n) :
    0 < containingOneCoefficientProbability (K := K) (2 * r + 2) 0 := by
  apply centered_energy_lt_inv_sq_implies_probability_pos n (2 * r + 2) hn
    (by omega) (by omega)
  exact centeredContainingOneProbability_even_energy_lt_inv_sq n r hn hr hnbound

omit [DecidableEq K] in
theorem containingOneCoefficientFiber_nonempty_of_probability_pos (n d : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 0 < d) (hdn : d ≤ n)
    (hprob : 0 < containingOneCoefficientProbability (K := K) d 0) :
    Nonempty (containingOneCoefficientFiber (K := K) d 0) := by
  classical
  have hdenNat := dimensionFiberContainingOne_card_pos n d hn (by omega) hdn
  have hden : 0 < (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ) := by
    exact_mod_cast hdenNat
  have hnumReal : 0 < (Nat.card (containingOneCoefficientFiber (K := K) d 0) : ℝ) := by
    by_contra hnot
    have hnum : (Nat.card (containingOneCoefficientFiber (K := K) d 0) : ℝ) ≤ 0 :=
      le_of_not_gt hnot
    have hprob' :
        (Nat.card (containingOneCoefficientFiber (K := K) d 0) : ℝ) /
          (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ) > 0 := by
      simpa [containingOneCoefficientProbability] using hprob
    have hquot :
        (Nat.card (containingOneCoefficientFiber (K := K) d 0) : ℝ) /
          (Nat.card (dimensionFiberContainingOne (K := K) d) : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum hden.le
    linarith
  have hcard : 0 < Nat.card (containingOneCoefficientFiber (K := K) d 0) := by
    exact_mod_cast hnumReal
  exact (Nat.card_pos_iff.mp hcard).1

theorem hasZeroSumSubspace_of_high_odd_dimension (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 5 ≤ r) (hnbound : 4 * r + 3 ≤ n) :
    HasZeroSumSubspace K (2 * r + 1) := by
  have hprob := containingOne_probability_zero_pos_odd_high (K := K) n r hn hr hnbound
  have hfiber := containingOneCoefficientFiber_nonempty_of_probability_pos
    (K := K) n (2 * r + 1) hn (by omega) (by omega) hprob
  obtain ⟨H⟩ := hfiber
  let E : {E : Submodule (ZMod 2) K //
      Module.finrank (ZMod 2) E = 2 * r + 1 ∧ nextFrobeniusCoefficient E = 0} :=
    ⟨H.val, H.property.1, H.property.2.2⟩
  let Z := nextCoefficientZeroEquivZeroSum (K := K) (2 * r + 1) (by omega) E
  exact ⟨Z.val, Z.property.1, Z.property.2⟩

theorem hasZeroSumSubspace_of_high_even_dimension (n r : ℕ)
    (hn : Module.finrank (ZMod 2) K = n)
    (hr : 4 ≤ r) (hnbound : 4 * r + 5 ≤ n) :
    HasZeroSumSubspace K (2 * r + 2) := by
  have hprob := containingOne_probability_zero_pos_even_high (K := K) n r hn hr hnbound
  have hfiber := containingOneCoefficientFiber_nonempty_of_probability_pos
    (K := K) n (2 * r + 2) hn (by omega) (by omega) hprob
  obtain ⟨H⟩ := hfiber
  let E : {E : Submodule (ZMod 2) K //
      Module.finrank (ZMod 2) E = 2 * r + 2 ∧ nextFrobeniusCoefficient E = 0} :=
    ⟨H.val, H.property.1, H.property.2.2⟩
  let Z := nextCoefficientZeroEquivZeroSum (K := K) (2 * r + 2) (by omega) E
  exact ⟨Z.val, Z.property.1, Z.property.2⟩

#print axioms centeredContainingOneProbability_sum_zero
#print axioms centeredContainingOneProbability_transfer
#print axioms centeredContainingOneProbability_twoStep_energy
#print axioms centeredContainingOneProbability_oneStep_energy
#print axioms centeredContainingOneProbability_odd_energy_bound
#print axioms centeredPairEnergyFactor_closed
#print axioms centeredContainingOneProbability_initial_energy
#print axioms centeredContainingOneProbability_odd_energy_explicit
#print axioms centeredContainingOneProbability_even_energy_explicit
#print axioms odd_energy_exponent_lt
#print axioms even_energy_exponent_lt
#print axioms energyFactor_lt_inv_sq_of_exponent
#print axioms field_card_eq_pow_finrank_local
#print axioms pairEnergyCondition_of_dimension_bound
#print axioms centeredContainingOneProbability_odd_energy_lt_inv_sq
#print axioms centeredContainingOneProbability_even_energy_lt_inv_sq
#print axioms centered_energy_lt_inv_sq_implies_probability_pos
#print axioms containingOne_probability_zero_pos_odd_high
#print axioms containingOne_probability_zero_pos_even_high
#print axioms containingOneCoefficientFiber_nonempty_of_probability_pos
#print axioms hasZeroSumSubspace_of_high_odd_dimension
#print axioms hasZeroSumSubspace_of_high_even_dimension

end Carlet
