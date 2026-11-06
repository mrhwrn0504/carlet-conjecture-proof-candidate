import Carlet.K4RootBoundProbe
noncomputable section
namespace Carlet
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
omit [Fintype K] [DecidableEq K] in
lemma k4_translate_u (t : K) : (t+1)^2+(t+1) = t^2+t := by
  have h2 : (2:K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (t+1)*h2
omit [Fintype K] [DecidableEq K] in
lemma k4_translate_d (t : K) : k4Denominator (t+1) = k4Denominator t := by
  simp only [k4Denominator, k4_translate_u]
omit [Fintype K] [DecidableEq K] in
lemma k4_translate_six (t : K) : (t+1)^6 = t^6+(t^2+t)^2+1 := by
  have h2 : (2:K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (3*t^5+7*t^4+9*t^3+7*t^2+3*t)*h2
omit [Fintype K] [DecidableEq K] in
lemma k4_sign0_translate (t : K) : k4Sign0 (t+1) = k4Sign0 t := by
  simp [k4Sign0, k4_translate_d]
omit [Fintype K] [DecidableEq K] in
lemma k4_sign1_translate (t : K) : k4Sign1 (t+1) = k4Sign1 t := by
  simp only [k4Sign1, k4_translate_d, k4_translate_u]
omit [Fintype K] [DecidableEq K] in
lemma k4_sign2_translate (t : K) :
    k4Sign2 (t+1) = k4Sign2 t * k4Sign1 t * k4Sign0 t := by
  simp only [k4Sign2, k4Sign1, k4Sign0, k4_translate_d, k4_translate_six]
  rw [add_div, add_div, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
omit [Fintype K] [DecidableEq K] in
lemma k4_translate_invol (t : K) : t+1+1 = t := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
lemma k4_translate_mem (t : K) : t ∈ k4Admissible (K := K) ↔ t+1 ∈ k4Admissible (K := K) := by
  simp only [k4Admissible, Finset.mem_filter, Finset.mem_univ, true_and, k4_translate_d]
lemma k4_sum_translate (f : K → ℝ) :
    (∑ t ∈ k4Admissible (K := K), f t) =
      ∑ t ∈ k4Admissible (K := K), f (t+1) := by
  symm
  apply Finset.sum_bij' (fun t _ => t+1) (fun t _ => t+1)
  · intro t ht; exact k4_translate_invol t
  · intro t ht; exact k4_translate_invol t
  · intro t ht; rfl
  · intro t ht; exact (k4_translate_mem t).mp ht
  · intro t ht; exact (k4_translate_mem t).mp ht
omit [Fintype K] [DecidableEq K] in
lemma k4_sign_square (x : K) : traceCharacter x * traceCharacter x = 1 := by
  rcases k4_trace_sign x with h | h <;> rw [h] <;> norm_num

lemma k4_sum2_eq_sum012 :
    (∑ t ∈ k4Admissible (K := K), k4Sign2 t) =
      ∑ t ∈ k4Admissible (K := K), k4Sign0 t * k4Sign1 t * k4Sign2 t := by
  rw [k4_sum_translate k4Sign2]
  apply Finset.sum_congr rfl
  intro t ht
  rw [k4_sign2_translate]
  ring

lemma k4_sum02_eq_sum12 :
    (∑ t ∈ k4Admissible (K := K), k4Sign0 t * k4Sign2 t) =
      ∑ t ∈ k4Admissible (K := K), k4Sign1 t * k4Sign2 t := by
  rw [k4_sum_translate (fun t => k4Sign0 t * k4Sign2 t)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [k4_sign0_translate, k4_sign2_translate]
  have hs : k4Sign0 t * k4Sign0 t = 1 := k4_sign_square _
  calc
    _ = (k4Sign0 t * k4Sign0 t) * (k4Sign1 t * k4Sign2 t) := by ring
    _ = _ := by rw [hs, one_mul]

/-- Translation symmetry reduces the seven independent lower bounds to five. -/
theorem hasZeroSumSubspace_four_of_five_character_bounds (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (hq : 8192 ≤ Fintype.card K)
    (h0 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x)
    (h1 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign1 x)
    (h2 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign2 x)
    (h01 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign1 x)
    (h02 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤ ∑ x ∈ (k4Admissible (K := K)), k4Sign0 x * k4Sign2 x) :
    HasZeroSumSubspace K 4 := by
  have h12 := h02
  rw [k4_sum02_eq_sum12] at h12
  have h012 := h2
  rw [k4_sum2_eq_sum012] at h012
  exact hasZeroSumSubspace_four_of_genus_five_bounds n hn hodd hq h0 h1 h2 h01 h02 h12 h012

omit [Fintype K] [DecidableEq K] in
lemma k4_denom_poly (t : K) : k4Denominator t = t^6+t^5+t^4+t^3+t^2+t+1 := by
  unfold k4Denominator
  have h2 : (2:K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (t^5+t^4)*h2

omit [Fintype K] [DecidableEq K] in
lemma k4_denom_invert (t : K) (ht : t ≠ 0) :
    k4Denominator t⁻¹ = k4Denominator t / t^6 := by
  rw [k4_denom_poly, k4_denom_poly]
  field_simp
  ring

omit [Fintype K] [DecidableEq K] in
lemma k4_sign0_invert (t : K) (ht : t ≠ 0) : k4Sign0 t⁻¹ = k4Sign2 t := by
  simp only [k4Sign0, k4Sign2, k4_denom_invert t ht]
  congr 1
  field_simp

omit [Fintype K] [DecidableEq K] in
lemma k4_sign1_invert (t : K) (ht : t ≠ 0) : k4Sign1 t⁻¹ = k4Sign1 t := by
  apply congrArg traceCharacter
  rw [k4_denom_invert t ht]
  field_simp
  ring

lemma k4_admissible_invert (t : K) (ht : t ≠ 0) :
    t ∈ k4Admissible (K := K) ↔ t⁻¹ ∈ k4Admissible (K := K) := by
  simp only [k4Admissible, Finset.mem_filter, Finset.mem_univ, true_and,
    k4_denom_invert t ht, div_ne_zero_iff]
  exact ⟨fun h => ⟨h, pow_ne_zero 6 ht⟩, And.left⟩

lemma k4_sum0_eq_sum2_without_zero :
    (∑ t ∈ (k4Admissible (K := K)).erase 0, k4Sign0 t) =
      ∑ t ∈ (k4Admissible (K := K)).erase 0, k4Sign2 t := by
  apply Finset.sum_bij' (fun t _ => t⁻¹) (fun t _ => t⁻¹)
  · intro t ht; exact inv_inv t
  · intro t ht; exact inv_inv t
  · intro t ht
    have hn := (Finset.mem_erase.mp ht).1
    simpa using k4_sign0_invert t⁻¹ (inv_ne_zero hn)
  · intro t ht
    have hm := Finset.mem_erase.mp ht
    exact Finset.mem_erase.mpr ⟨inv_ne_zero hm.1, (k4_admissible_invert t hm.1).mp hm.2⟩
  · intro t ht
    have hm := Finset.mem_erase.mp ht
    exact Finset.mem_erase.mpr ⟨inv_ne_zero hm.1, (k4_admissible_invert t hm.1).mp hm.2⟩

lemma k4_sum0_eq_sum2_sub_two (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) :
    (∑ t ∈ k4Admissible (K := K), k4Sign0 t) =
      (∑ t ∈ k4Admissible (K := K), k4Sign2 t) - 2 := by
  have hzero : (0 : K) ∈ k4Admissible := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [k4Denominator]⟩
  have htrace_one := Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2)
  simp only [map_one, hn, nsmul_eq_mul, mul_one, hodd.natCast_zmod_two] at htrace_one
  have hs0 : k4Sign0 (0 : K) = -1 := by
    simp [k4Sign0, k4Denominator, traceCharacter, binaryCharacter, htrace_one]
  have hs2 : k4Sign2 (0 : K) = 1 := by
    simp [k4Sign2, k4Denominator, traceCharacter, binaryCharacter]
  have ha := Finset.sum_erase_add (k4Admissible (K := K)) k4Sign0 hzero
  have hb := Finset.sum_erase_add (k4Admissible (K := K)) k4Sign2 hzero
  have hc := k4_sum0_eq_sum2_without_zero (K := K)
  linarith

lemma k4_sum01_erase_eq_sum12_erase :
    (∑ t ∈ (k4Admissible (K := K)).erase 0, k4Sign0 t * k4Sign1 t) =
      ∑ t ∈ (k4Admissible (K := K)).erase 0, k4Sign1 t * k4Sign2 t := by
  apply Finset.sum_bij' (fun t _ => t⁻¹) (fun t _ => t⁻¹)
  · intro t ht; exact inv_inv t
  · intro t ht; exact inv_inv t
  · intro t ht
    have hn : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have h0 : k4Sign0 t = k4Sign2 t⁻¹ := by
      simpa using (k4_sign0_invert t⁻¹ (inv_ne_zero hn))
    have h1 : k4Sign1 t = k4Sign1 t⁻¹ := (k4_sign1_invert t hn).symm
    rw [h0, h1]
    ring
  · intro t ht
    have hm := Finset.mem_erase.mp ht
    exact Finset.mem_erase.mpr ⟨inv_ne_zero hm.1, (k4_admissible_invert t hm.1).mp hm.2⟩
  · intro t ht
    have hm := Finset.mem_erase.mp ht
    exact Finset.mem_erase.mpr ⟨inv_ne_zero hm.1, (k4_admissible_invert t hm.1).mp hm.2⟩

lemma k4_sum01_eq_sum02_sub_two (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) :
    (∑ t ∈ k4Admissible (K := K), k4Sign0 t * k4Sign1 t) =
      (∑ t ∈ k4Admissible (K := K), k4Sign0 t * k4Sign2 t) - 2 := by
  have hzero : (0 : K) ∈ k4Admissible := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [k4Denominator]⟩
  have htrace_one := Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2)
  simp only [map_one, hn, nsmul_eq_mul, mul_one, hodd.natCast_zmod_two] at htrace_one
  have hs0 : k4Sign0 (0 : K) = -1 := by
    simp [k4Sign0, k4Denominator, traceCharacter, binaryCharacter, htrace_one]
  have hs1 : k4Sign1 (0 : K) = 1 := by
    simp [k4Sign1, k4Denominator, traceCharacter, binaryCharacter]
  have hs2 : k4Sign2 (0 : K) = 1 := by
    simp [k4Sign2, k4Denominator, traceCharacter, binaryCharacter]
  have ha := Finset.sum_erase_add (k4Admissible (K := K))
    (fun t => k4Sign0 t * k4Sign1 t) hzero
  have hb := Finset.sum_erase_add (k4Admissible (K := K))
    (fun t => k4Sign1 t * k4Sign2 t) hzero
  rw [hs0, hs1] at ha
  rw [hs1, hs2] at hb
  have hc := k4_sum01_erase_eq_sum12_erase (K := K)
  have hd := k4_sum02_eq_sum12 (K := K)
  linarith

/-- Only three of the seven character sums are needed; inversion and
    translation recover the other four, with the zero-parameter correction. -/
theorem hasZeroSumSubspace_four_of_three_character_bounds (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n)
    (hq : 8192 ≤ Fintype.card K)
    (h0 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤
      ∑ x ∈ k4Admissible (K := K), k4Sign0 x)
    (h1 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤
      ∑ x ∈ k4Admissible (K := K), k4Sign1 x)
    (h02 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤
      ∑ x ∈ k4Admissible (K := K), k4Sign0 x * k4Sign2 x) :
    HasZeroSumSubspace K 4 := by
  let B : ℝ := 10 * Real.sqrt (Fintype.card K : ℝ) + 3
  have hqR : (8192 : ℝ) ≤ Fintype.card K := by exact_mod_cast hq
  have hroot : 90 ≤ Real.sqrt (Fintype.card K : ℝ) := by
    have hsq := Real.sq_sqrt (show 0 ≤ (Fintype.card K : ℝ) by positivity)
    have hr0 := Real.sqrt_nonneg (Fintype.card K : ℝ)
    nlinarith [hsq, hqR, hr0, show (90 : ℝ) ^ 2 = 8100 by norm_num]
  have hsq := Real.sq_sqrt (show 0 ≤ (Fintype.card K : ℝ) by positivity)
  have hmargin : 7 * B + 6 < (Fintype.card K : ℝ) := by
    dsimp [B]
    nlinarith
  have hsize := k4_admissible_size_condition (K := K) B hmargin
  have hsum02 := k4_sum0_eq_sum2_sub_two (K := K) n hn hodd
  have h2 : -(10 * Real.sqrt (Fintype.card K : ℝ) + 1) ≤
      ∑ x ∈ k4Admissible (K := K), k4Sign2 x := by
    linarith
  have h012 : -B ≤ ∑ x ∈ k4Admissible (K := K),
      k4Sign0 x * k4Sign1 x * k4Sign2 x := by
    rw [← k4_sum2_eq_sum012 (K := K)]
    dsimp [B]
    linarith [h2]
  have h12 : -B ≤ ∑ x ∈ k4Admissible (K := K), k4Sign1 x * k4Sign2 x := by
    rw [← k4_sum02_eq_sum12 (K := K)]
    dsimp [B]
    linarith [h02]
  have h01 : -B ≤ ∑ x ∈ k4Admissible (K := K), k4Sign0 x * k4Sign1 x := by
    rw [k4_sum01_eq_sum02_sub_two (K := K) n hn hodd]
    dsimp [B]
    linarith [h02]
  have h0' : -B ≤ ∑ x ∈ k4Admissible (K := K), k4Sign0 x := by
    dsimp [B]
    linarith [h0]
  have h1' : -B ≤ ∑ x ∈ k4Admissible (K := K), k4Sign1 x := by
    dsimp [B]
    linarith [h1]
  have h02' : -B ≤ ∑ x ∈ k4Admissible (K := K), k4Sign0 x * k4Sign2 x := by
    dsimp [B]
    linarith [h02]
  have h2' : -B ≤ ∑ x ∈ k4Admissible (K := K), k4Sign2 x := by
    dsimp [B]
    linarith [h2]
  exact hasZeroSumSubspace_four_of_seven_character_bounds n hn hodd B
    h0' h1' h2' h01 h02' h12 h012 hsize

#print axioms k4_sign1_invert
#print axioms k4_sum01_erase_eq_sum12_erase
#print axioms k4_sum01_eq_sum02_sub_two
#print axioms hasZeroSumSubspace_four_of_three_character_bounds

#print axioms k4_sum0_eq_sum2_sub_two
#print axioms k4_sum0_eq_sum2_without_zero
#print axioms k4_admissible_invert
#print axioms k4_sign0_invert
#print axioms k4_denom_invert
#print axioms hasZeroSumSubspace_four_of_five_character_bounds
#print axioms k4_sum2_eq_sum012
#print axioms k4_sum02_eq_sum12
end Carlet
















