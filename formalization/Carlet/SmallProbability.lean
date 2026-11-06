import Carlet.ConcreteProbabilityRecursion

noncomputable section

open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- The actual two-dimensional distribution, including its exceptional value at 1. -/
theorem containingOne_probability_two_dim (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hn2 : 2 ≤ n) (b : K) :
    containingOneCoefficientProbability (K := K) 2 b =
      if b = 1 then 0 else
        (1 + traceCharacter (K := K) (b + 1)) / ((Fintype.card K : ℝ) - 2) := by
  have hp1 : containingOneCoefficientProbability (K := K) 1 =
      fun v : K => if v = 1 then 1 else 0 := by
    funext v
    exact containingOne_probability_one_dim n hn (by omega) v
  have ht := containingOne_probability_transfer (K := K) n 1 hn (by omega) (by omega) b
  rw [hp1] at ht
  by_cases hb : b = 1
  · subst b
    simpa [Transfer.transfer, Transfer.coreTransfer, Transfer.transferNumerator] using ht.symm
  · have hsub : b - 1 ≠ 0 := sub_ne_zero.mpr hb
    have hsum :
        (∑ v ∈ Transfer.nonzeroElements (K := K),
          (1 + traceCharacter (K := K) ((b - 1) / v)) *
            (if v = 1 then (1 : ℝ) else 0)) =
          1 + traceCharacter (K := K) (b - 1) := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro v hv hv1
        simp [hv1]
      · simp [Transfer.nonzeroElements]
    have hshift : b - 1 = b + 1 := CharTwo.sub_eq_add b 1
    rw [if_neg hb]
    change (Transfer.transfer _ _ _ b) = _ at ht
    rw [Transfer.transfer, Transfer.coreTransfer, Transfer.transferNumerator, if_neg hsub] at ht
    norm_num only [pow_one, Nat.cast_ofNat, Nat.cast_one] at ht
    simp only [one_mul] at ht
    rw [hsum, hshift] at ht
    exact ht.symm

omit [Fintype K] [DecidableEq K] in
theorem traceCharacter_one_of_odd_finrank (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) :
    traceCharacter (K := K) 1 = -1 := by
  have htrace := Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2)
  simp only [map_one, hn, nsmul_eq_mul, mul_one, hodd.natCast_zmod_two] at htrace
  change (if Algebra.trace (ZMod 2) K 1 = 0 then (1 : ℝ) else -1) = -1
  simp [htrace]

theorem containingOne_probability_two_zero_of_odd (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hn2 : 2 ≤ n) (hodd : Odd n) :
    containingOneCoefficientProbability (K := K) 2 0 = 0 := by
  rw [containingOne_probability_two_dim n hn hn2]
  simp [traceCharacter_one_of_odd_finrank n hn hodd]

/-- The first genuinely nontrivial zero-coordinate recurrence in odd degree. -/
theorem containingOne_probability_three_zero (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hn3 : 3 ≤ n) (hodd : Odd n) :
    ((Fintype.card K : ℝ) - 4) * containingOneCoefficientProbability (K := K) 3 0 =
      1 + 3 * (∑ v ∈ Transfer.nonzeroElements (K := K),
        traceCharacter (K := K) (v⁻¹) * containingOneCoefficientProbability (K := K) 2 v) := by
  have h := containingOne_probability_recursion (K := K) n 2 hn (by omega) (by omega)
    0 (by simp)
  rw [containingOne_probability_two_zero_of_odd n hn (by omega) hodd] at h
  simp only [zero_add] at h
  rw [normalizedReciprocalFiberSum_finset 2 1 one_ne_zero] at h
  norm_num only [zero_add, one_div, sub_zero, pow_succ, pow_zero, mul_one] at h
  exact h

#print axioms containingOne_probability_two_dim
#print axioms traceCharacter_one_of_odd_finrank
#print axioms containingOne_probability_two_zero_of_odd
#print axioms containingOne_probability_three_zero

end Carlet
