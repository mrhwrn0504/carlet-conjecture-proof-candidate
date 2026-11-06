import Carlet.FivePolynomialRoots
import Carlet.SmallFrobenius
import Carlet.RemainingCases
noncomputable section
open Polynomial
namespace Carlet
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def smallMap2 : K →ₗ[ZMod 2] K where
  toFun := smallL2
  map_add' := by intro x y; simp only [smallL2, add_pow_char_pow]; ring
  map_smul' := by
    intro a x
    fin_cases a
    · change smallL2 ((0 : ZMod 2) • x) = (0 : ZMod 2) • smallL2 x
      simp [smallL2]
    · change smallL2 ((1 : ZMod 2) • x) = (1 : ZMod 2) • smallL2 x
      simp

def smallMap3 : K →ₗ[ZMod 2] K where
  toFun := smallL3
  map_add' := by intro x y; simp only [smallL3, add_pow_char_pow]; ring
  map_smul' := by
    intro a x
    fin_cases a
    · change smallL3 ((0 : ZMod 2) • x) = (0 : ZMod 2) • smallL3 x
      simp [smallL3]
    · change smallL3 ((1 : ZMod 2) • x) = (1 : ZMod 2) • smallL3 x
      simp

theorem small_poly_kernel_card (f : K →ₗ[ZMod 2] K) (p : K[X])
    (hmonic : p.Monic) (hsep : p.Separable) (hsplit : p.Splits)
    (heval : ∀ x, p.eval x = f x) : Nat.card (LinearMap.ker f) = p.natDegree := by
  classical
  let : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  rw [← Fintype.card_eq_nat_card, Fintype.card_subtype]
  change (underlyingFinset (LinearMap.ker f)).card = p.natDegree
  have hset : underlyingFinset (LinearMap.ker f) = p.roots.toFinset := by
    ext x
    simp only [mem_underlyingFinset, LinearMap.mem_ker, Multiset.mem_toFinset,
      Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot, heval]
  rw [hset, Multiset.toFinset_card_of_nodup (nodup_roots hsep), ← hsplit.natDegree_eq_card_roots]

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem smallL2_monic : (smallL2 (X : K[X])).Monic := by
  unfold smallL2
  norm_num only
  monicity <;> norm_num

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem smallL3_monic : (smallL3 (X : K[X])).Monic := by
  unfold smallL3
  norm_num only
  monicity <;> norm_num

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem smallL2_degree : (smallL2 (X : K[X])).natDegree = 4 := by
  unfold smallL2
  norm_num only
  compute_degree!

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem smallL3_degree : (smallL3 (X : K[X])).natDegree = 8 := by
  unfold smallL3
  norm_num only
  compute_degree!

omit [Fintype K] [DecidableEq K] in
theorem smallL2_separable : (smallL2 (X : K[X])).Separable := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) + 1 = 0 := by linear_combination (2 : K) * htwo
  have h1 : (1 : K) + 1 = 0 := by linear_combination htwo
  have hc3 : C (3 : K) + 1 = 0 := by rw [← C_1, ← map_add, h3, map_zero]
  have hc1 : C (1 : K) + 1 = 0 := by rw [← C_1, ← map_add, h1, map_zero]
  have hc11 : (1 : K[X]) + 1 = 0 := by simpa using hc1
  rw [separable_def]
  have hderiv : derivative (smallL2 (X : K[X])) = 1 := by simp [smallL2, hc3, hc11]
  rw [hderiv]
  exact isCoprime_one_right

omit [Fintype K] [DecidableEq K] in
theorem smallL3_separable : (smallL3 (X : K[X])).Separable := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h7 : (7 : K) + 1 = 0 := by linear_combination (4 : K) * htwo
  have h1 : (1 : K) + 1 = 0 := by linear_combination htwo
  have hc7 : C (7 : K) + 1 = 0 := by rw [← C_1, ← map_add, h7, map_zero]
  have hc1 : C (1 : K) + 1 = 0 := by rw [← C_1, ← map_add, h1, map_zero]
  have hc11 : (1 : K[X]) + 1 = 0 := by simpa using hc1
  rw [separable_def]
  have hderiv : derivative (smallL3 (X : K[X])) = 1 := by simp [smallL3, hc7, hc11]
  rw [hderiv]
  exact isCoprime_one_right

theorem smallMap2_finrank (hs : (smallL2 (X : K[X])).Splits) :
    Module.finrank (ZMod 2) (LinearMap.ker (smallMap2 (K := K))) = 2 := by
  classical
  let E := LinearMap.ker (smallMap2 (K := K))
  have heval (x : K) : (smallL2 (X : K[X])).eval x = smallMap2 x := by simp [smallL2, smallMap2]
  have hc : Nat.card E = 4 := by
    simpa [E, smallL2_degree] using small_poly_kernel_card (smallMap2 (K := K))
      (smallL2 (X : K[X])) smallL2_monic smallL2_separable hs heval
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
  rw [Nat.card_zmod] at hpow
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) E = Nat.card E := hpow.symm
    _ = 4 := hc
    _ = 2 ^ 2 := by norm_num

theorem smallMap3_finrank (hs : (smallL3 (X : K[X])).Splits) :
    Module.finrank (ZMod 2) (LinearMap.ker (smallMap3 (K := K))) = 3 := by
  classical
  let E := LinearMap.ker (smallMap3 (K := K))
  have heval (x : K) : (smallL3 (X : K[X])).eval x = smallMap3 x := by simp [smallL3, smallMap3]
  have hc : Nat.card E = 8 := by
    simpa [E, smallL3_degree] using small_poly_kernel_card (smallMap3 (K := K))
      (smallL3 (X : K[X])) smallL3_monic smallL3_separable hs heval
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
  rw [Nat.card_zmod] at hpow
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) E = Nat.card E := hpow.symm
    _ = 8 := hc
    _ = 2 ^ 3 := by norm_num

omit [Fintype K] [DecidableEq K] in
theorem small_kernels_disjoint :
    Disjoint (LinearMap.ker (smallMap2 (K := K))) (LinearMap.ker (smallMap3 (K := K))) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have h2 : x^4 + x^2 + x = 0 := by
    have h := (LinearMap.mem_ker.mp hx.1)
    simpa [smallMap2, smallL2] using h
  have h3 : x^8 + x^2 + x = 0 := by
    have h := (LinearMap.mem_ker.mp hx.2)
    simpa [smallMap3, smallL3] using h
  have hs : x^8 + x^4 + x^2 = 0 := by
    have h := congrArg (fun z : K => z^2) h2
    simp only [add_pow_char, ← pow_mul] at h
    norm_num at h ⊢
    exact h
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : x^2 = 0 := by linear_combination h3 - hs + h2 - htwo * x
  have hx0 : x = 0 := eq_zero_of_pow_eq_zero hsq
  simpa using hx0

theorem five_poly_splits_of_small_splits
    (hs2 : (smallL2 (X : K[X])).Splits) (hs3 : (smallL3 (X : K[X])).Splits) :
    (linearizedP (X : K[X])).Splits := by
  classical
  let U := LinearMap.ker (smallMap2 (K := K))
  let V := LinearMap.ker (smallMap3 (K := K))
  let E := U ⊔ V
  have hU : U ≤ LinearMap.ker (fiveLinearMap (K := K)) := by
    intro x hx
    have hx2 : smallL2 x = 0 := LinearMap.mem_ker.mp hx
    apply LinearMap.mem_ker.mpr
    change linearizedP x = 0
    rw [← (smallL_composition x).2, hx2]
    simp [smallL3]
  have hV : V ≤ LinearMap.ker (fiveLinearMap (K := K)) := by
    intro x hx
    have hx3 : smallL3 x = 0 := LinearMap.mem_ker.mp hx
    apply LinearMap.mem_ker.mpr
    change linearizedP x = 0
    rw [← (smallL_composition x).1, hx3]
    simp [smallL2]
  have hE : E ≤ LinearMap.ker (fiveLinearMap (K := K)) := sup_le hU hV
  have hdim : Module.finrank (ZMod 2) E = 5 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U V
    have hd : U ⊓ V = ⊥ := small_kernels_disjoint.eq_bot
    rw [hd, finrank_bot, add_zero, smallMap2_finrank hs2, smallMap3_finrank hs3] at h
    exact h
  have hcard : (underlyingFinset E).card = 32 := by
    let : Fintype E := Fintype.ofFinite E
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [Nat.card_zmod, hdim] at hnat
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hnat
    norm_num at hnat
    exact hnat
  have hsubset : (underlyingFinset E).val ⊆ (linearizedP (X : K[X])).roots := by
    intro x hx
    have hxE : x ∈ E := (mem_underlyingFinset E x).mp (Finset.mem_val.mp hx)
    have hxP : fiveLinearMap x = 0 := LinearMap.mem_ker.mp (hE hxE)
    apply (Polynomial.mem_roots (five_poly_monic (K := K)).ne_zero).mpr
    change (linearizedP (X : K[X])).eval x = 0
    rw [five_poly_eval, hxP]
  have hle : 32 ≤ (linearizedP (X : K[X])).roots.card := by
    have h := Multiset.card_le_card (Finset.val_le_iff_val_subset.mpr hsubset)
    simpa [hcard] using h
  apply Polynomial.splits_iff_card_roots.mpr
  have hu := Polynomial.card_roots' (linearizedP (X : K[X]))
  rw [five_poly_degree] at hu ⊢
  omega

theorem hasZeroSumSubspace_five_of_21_dvd (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 21 ∣ n) : HasZeroSumSubspace K 5 := by
  have h3 : 3 ∣ n := dvd_trans (by norm_num : 3 ∣ 21) hd
  have h7 : 7 ∣ n := dvd_trans (by norm_num : 7 ∣ 21) hd
  have hs2 := smallL2_splits_of_three_dvd n hn h3
  have hs3 := smallL3_splits_of_seven_dvd n hn h7
  exact hasZeroSumSubspace_five_of_polynomial_splits (five_poly_splits_of_small_splits hs2 hs3)

theorem oddCarletConjecture_iff_four_and_five_remaining :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n → (k = 4 ∨ k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 21 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk hbound K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_four_and_five_coprime.mpr
    intro n k hn hk hbound K _ _ _ hcard
    rcases hk with hk | ⟨hk, h5⟩
    · exact h n k hn (Or.inl hk) hbound K hcard
    · by_cases h21 : 21 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_21_dvd n (finrank_eq_of_card n hcard) h21
      · exact h n k hn (Or.inr ⟨hk, h5, h21⟩) hbound K hcard

#print axioms oddCarletConjecture_iff_four_and_five_remaining
#print axioms five_poly_splits_of_small_splits
#print axioms hasZeroSumSubspace_five_of_21_dvd
#print axioms small_kernels_disjoint
#print axioms smallMap2_finrank
#print axioms smallMap3_finrank
#print axioms smallL2_separable
#print axioms smallL3_separable
#print axioms small_poly_kernel_card
end Carlet
