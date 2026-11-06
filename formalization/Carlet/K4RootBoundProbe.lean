import Carlet.K4CharacterReductionProbe
import Mathlib.Analysis.SpecialFunctions.Sqrt
noncomputable section
open Polynomial
namespace Carlet
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
def k4Poly : K[X] := (X^2+X)^3+(X^2+X)+1
omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
lemma k4Poly_monic : (k4Poly (K := K)).Monic := by
  unfold k4Poly
  monicity <;> norm_num
omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
lemma k4Poly_degree : (k4Poly (K := K)).natDegree ≤ 6 := by
  unfold k4Poly
  have hu : ((X : K[X]) ^ 2 + X).natDegree ≤ 2 := by
    calc
      _ ≤ max ((X : K[X]) ^ 2).natDegree X.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by simp
  calc
    _ ≤ max (((X : K[X])^2+X)^3+((X : K[X])^2+X)).natDegree (1 : K[X]).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ 6 := by
      have h1 := Polynomial.natDegree_add_le (((X : K[X])^2+X)^3) ((X : K[X])^2+X)
      have h2 := Polynomial.natDegree_pow_le (p := ((X : K[X])^2+X)) (n := 3)
      simp only [Polynomial.natDegree_one] at *
      omega
omit [Algebra (ZMod 2) K] in
lemma k4_bad_card : (Finset.univ.filter (fun t : K => k4Denominator t = 0)).card ≤ 6 := by
  classical
  have hp : (k4Poly (K := K)) ≠ 0 := k4Poly_monic.ne_zero
  calc
    _ ≤ (k4Poly (K := K)).roots.toFinset.card := by
      apply Finset.card_le_card
      intro t ht
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hp).2
      change (k4Poly (K := K)).eval t = 0
      simpa [k4Poly, k4Denominator] using (Finset.mem_filter.mp ht).2
    _ ≤ (k4Poly (K := K)).roots.card := Multiset.toFinset_card_le _
    _ ≤ (k4Poly (K := K)).natDegree := Polynomial.card_roots' _
    _ ≤ 6 := k4Poly_degree
omit [Algebra (ZMod 2) K] in
lemma k4_admissible_card : Fintype.card K ≤ (k4Admissible (K := K)).card + 6 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K)) (fun t => k4Denominator t ≠ 0)
  simp only [not_ne_iff, Finset.card_univ] at h
  have hb := k4_bad_card (K := K)
  change (k4Admissible (K := K)).card + _ = _ at h
  omega
omit [Algebra (ZMod 2) K] in
lemma k4_admissible_size_condition (B : ℝ)
    (h : 7 * B + 6 < (Fintype.card K : ℝ)) :
    7 * B < ((k4Admissible (K := K)).card : ℝ) := by
  have hn := k4_admissible_card (K := K)
  have hr : (Fintype.card K : ℝ) ≤ (k4Admissible (K := K)).card + 6 := by
    exact_mod_cast hn
  linarith

omit [Algebra (ZMod 2) K] in
lemma k4_genus_five_size_condition (hq : 8192 ≤ Fintype.card K) :
    7 * (10 * Real.sqrt (Fintype.card K : ℝ) + 1) <
      ((k4Admissible (K := K)).card : ℝ) := by
  apply k4_admissible_size_condition
  have hqr : (8192 : ℝ) ≤ Fintype.card K := by exact_mod_cast hq
  have hm := k4_genus_five_numeric_margin (Fintype.card K : ℝ) hqr
  linarith

/-- For fields of size at least 2^13, seven genus-five-type character bounds suffice. -/
theorem hasZeroSumSubspace_four_of_genus_five_bounds (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n)
    (hq : 8192 ≤ Fintype.card K)
    (h0 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x)
    (h1 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign1 x)
    (h2 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign2 x)
    (h01 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign1 x)
    (h02 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign2 x)
    (h12 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign1 x * k4Sign2 x)
    (h012 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign1 x * k4Sign2 x) :
    HasZeroSumSubspace K 4 := by
  exact hasZeroSumSubspace_four_of_seven_character_bounds n hn hodd _
    h0 h1 h2 h01 h02 h12 h012 (k4_genus_five_size_condition hq)

/-- Numerical endpoint in the published Θ₄/Lang–Weil argument: the lower
    bound is positive for q ≥ 2^17. -/
theorem k4_theta4_lang_weil_numeric_margin (q : ℝ) (hq : 131072 ≤ q) :
    0 < q - 48 * Real.sqrt q - 41185 := by
  have hq0 : 0 ≤ q := by linarith
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
  have hs360 : 360 ≤ Real.sqrt q := by nlinarith
  have hp := mul_nonneg (show 0 ≤ Real.sqrt q - 360 by linarith)
    (show 0 ≤ Real.sqrt q + 312 by linarith)
  nlinarith

theorem k4_theta4_lang_weil_numeric_margin_pow (n : ℕ) (hn : 17 ≤ n) :
    0 < (2 : ℝ) ^ n - 48 * Real.sqrt ((2 : ℝ) ^ n) - 41185 := by
  have hpNat : 2 ^ 17 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hpReal : (131072 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc
      (131072 : ℝ) = (2 : ℝ) ^ 17 := by norm_num
      _ ≤ (2 : ℝ) ^ n := by exact_mod_cast hpNat
  exact k4_theta4_lang_weil_numeric_margin ((2 : ℝ) ^ n) hpReal

#print axioms hasZeroSumSubspace_four_of_genus_five_bounds
#print axioms k4_theta4_lang_weil_numeric_margin
#print axioms k4_theta4_lang_weil_numeric_margin_pow
end Carlet






