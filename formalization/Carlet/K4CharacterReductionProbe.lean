import Carlet.K4ParametricExtensionProbe
import Carlet.K4TraceCountingProbe

noncomputable section
open scoped BigOperators
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def k4Denominator (t : K) : K := (t^2+t)^3+(t^2+t)+1
def k4Admissible : Finset K := Finset.univ.filter (fun t => k4Denominator t ≠ 0)
def k4Sign0 (t : K) : ℝ := traceCharacter (1 / k4Denominator t)
def k4Sign1 (t : K) : ℝ := traceCharacter ((t^2+t)^2 / k4Denominator t)
def k4Sign2 (t : K) : ℝ := traceCharacter (t^6 / k4Denominator t)

omit [Fintype K] [DecidableEq K] in
theorem k4_trace_sign (x : K) : traceCharacter x = 1 ∨ traceCharacter x = -1 := by
  classical
  change (if Algebra.trace (ZMod 2) K x = 0 then (1 : ℝ) else -1) = 1 ∨
    (if Algebra.trace (ZMod 2) K x = 0 then (1 : ℝ) else -1) = -1
  split_ifs <;> simp

/-- A precise conditional reduction to seven character-sum lower bounds. -/
theorem hasZeroSumSubspace_four_of_seven_character_bounds (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (B : ℝ)
    (h0 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x)
    (h1 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign1 x)
    (h2 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign2 x)
    (h01 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign1 x)
    (h02 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign2 x)
    (h12 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign1 x * k4Sign2 x)
    (h012 : -B ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign1 x * k4Sign2 x)
    (hsize : 7*B < (k4Admissible (K := K)).card) : HasZeroSumSubspace K 4 := by
  classical
  obtain ⟨t, ht, ht0, ht1, ht2⟩ := triple_sign_exists_of_sum_bounds
    (k4Admissible (K := K)) k4Sign0 k4Sign1 k4Sign2 B
    (by intro x hx; exact k4_trace_sign _)
    (by intro x hx; exact k4_trace_sign _)
    (by intro x hx; exact k4_trace_sign _)
    h0 h1 h2 h01 h02 h12 h012 hsize
  have hd : k4Denominator t ≠ 0 := (Finset.mem_filter.mp ht).2
  have htrace0 : Algebra.trace (ZMod 2) K (1 / k4Denominator t) = 0 :=
    (traceCharacter_eq_one_iff _).mp ht0
  have htrace1 : Algebra.trace (ZMod 2) K ((t^2+t)^2 / k4Denominator t) = 0 :=
    (traceCharacter_eq_one_iff _).mp ht1
  have htrace2 : Algebra.trace (ZMod 2) K (t^6 / k4Denominator t) = 0 :=
    (traceCharacter_eq_one_iff _).mp ht2
  have htrace_one := Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2)
  simp only [map_one, hn, nsmul_eq_mul, mul_one, hodd.natCast_zmod_two] at htrace_one
  have hu : t^2+t ≠ 0 := by
    intro h
    have hd1 : k4Denominator t = 1 := by simp [k4Denominator, h]
    rw [hd1] at htrace0
    simp only [div_one, htrace_one] at htrace0
    exact one_ne_zero htrace0
  have hu1 : t^2+t+1 ≠ 0 := by
    intro h
    have heq : t^2+t = 1 := CharTwo.add_eq_zero.mp h
    have htrace_u : Algebra.trace (ZMod 2) K (t^2+t) = 0 := by
      rw [map_add, trace_square, CharTwo.add_self_eq_zero]
    rw [heq, htrace_one] at htrace_u
    exact one_ne_zero htrace_u
  exact hasZeroSumSubspace_four_of_k4_rational_traces t hu hu1 hd htrace0 htrace1 htrace2

#print axioms hasZeroSumSubspace_four_of_seven_character_bounds
end Carlet
