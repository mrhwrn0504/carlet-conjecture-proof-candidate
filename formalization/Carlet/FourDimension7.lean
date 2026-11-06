import Carlet.FiveDimension31

noncomputable section
open Polynomial
namespace Carlet

def linearizedP4 {R : Type*} [CommRing R] (x : R) : R :=
  x^(2^4 : ℕ) + x^(2^3 : ℕ) + x^(2^2 : ℕ) + x

def linearizedQ4 {R : Type*} [CommRing R] (y : R) : R := y^(2^3 : ℕ) + y^(2^2 : ℕ) + y

theorem linearizedPQ4 {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    linearizedQ4 (linearizedP4 x) = x^(2^7 : ℕ) + x := by
  unfold linearizedP4 linearizedQ4
  simp only [add_pow_char_pow, ← pow_mul]
  ring_nf
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simp [htwo]

theorem linearizedQ4_dvd {R : Type*} [CommRing R] (y : R) : y ∣ linearizedQ4 y := by
  unfold linearizedQ4
  repeat' apply dvd_add
  all_goals first | exact dvd_refl y | exact dvd_pow_self y (by norm_num)

theorem linearizedP4_dvd {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    linearizedP4 x ∣ x^(2^7 : ℕ) + x := by
  rw [← linearizedPQ4 x]
  exact linearizedQ4_dvd _

set_option maxRecDepth 4096 in
theorem linearizedP4_splits_of_card {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hc : Fintype.card K = 128) : (linearizedP4 (X : K[X])).Splits := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  apply split_of_card_divides
  rw [hc]
  exact linearizedP4_dvd (X : K[X])

theorem linearizedP4_splits_of_seven_dvd {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (hd : 7 ∣ n) : (linearizedP4 (X : K[X])).Splits := by
  classical
  let L := GaloisField 2 7
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 7 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 128 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
    norm_num
  have hs : (linearizedP4 (X : L[X])).Splits := linearizedP4_splits_of_card hc
  have hdim : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by simpa [hr, hn] using hd
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdim
  have hm := hs.map f.toRingHom
  simpa only [linearizedP4, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X] using hm

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def fourLinearMap : K →ₗ[ZMod 2] K where
  toFun := linearizedP4
  map_add' := by intro x y; simp only [linearizedP4, add_pow_char_pow]; ring
  map_smul' := by
    intro a x
    fin_cases a
    · change linearizedP4 ((0 : ZMod 2) • x) = (0 : ZMod 2) • linearizedP4 x
      simp [linearizedP4]
    · change linearizedP4 ((1 : ZMod 2) • x) = (1 : ZMod 2) • linearizedP4 x
      simp

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem p4_monic : (linearizedP4 (X : K[X])).Monic := by
  unfold linearizedP4
  norm_num only
  monicity <;> norm_num

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem p4_coeff_two : (linearizedP4 (X : K[X])).coeff 2 = 0 := by
  simp [linearizedP4, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]

omit [Fintype K] [DecidableEq K] in
theorem p4_derivative : derivative (linearizedP4 (X : K[X])) = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h15 : (15 : K) + 1 = 0 := by linear_combination (8 : K) * htwo
  have h7 : (7 : K) + 1 = 0 := by linear_combination (4 : K) * htwo
  have h3 : (3 : K) + 1 = 0 := by linear_combination (2 : K) * htwo
  have hc15 : C (15 : K) + 1 = 0 := by rw [← C_1, ← map_add, h15, map_zero]
  have hc7 : C (7 : K) + 1 = 0 := by rw [← C_1, ← map_add, h7, map_zero]
  have hc3 : C (3 : K) + 1 = 0 := by rw [← C_1, ← map_add, h3, map_zero]
  simp [linearizedP4, hc15, hc7, hc3]

omit [Fintype K] [DecidableEq K] in
theorem p4_separable : (linearizedP4 (X : K[X])).Separable := by
  rw [separable_def, p4_derivative]
  exact isCoprime_one_right

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem p4_degree : (linearizedP4 (X : K[X])).natDegree = 16 := by
  unfold linearizedP4
  norm_num only
  compute_degree!

theorem p4_kernel_roots :
    underlyingFinset (LinearMap.ker (fourLinearMap (K := K))) =
      (linearizedP4 (X : K[X])).roots.toFinset := by
  classical
  ext x
  simp only [mem_underlyingFinset, LinearMap.mem_ker, Multiset.mem_toFinset,
    Polynomial.mem_roots p4_monic.ne_zero, Polynomial.IsRoot]
  simp [fourLinearMap, linearizedP4]

theorem p4_kernel_product (hsplit : (linearizedP4 (X : K[X])).Splits) :
    rootProduct (underlyingFinset (LinearMap.ker (fourLinearMap (K := K)))) =
      linearizedP4 (X : K[X]) := by
  classical
  rw [p4_kernel_roots]
  calc
    _ = ((linearizedP4 (X : K[X])).roots.map (fun x => X - C x)).prod := by
      unfold rootProduct
      simp only [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr
        (nodup_roots p4_separable), CharTwo.sub_eq_add]
    _ = _ := (hsplit.eq_prod_roots_of_monic p4_monic).symm

theorem hasZeroSumSubspace_four_of_polynomial4_splits
    (hsplit : (linearizedP4 (X : K[X])).Splits) : HasZeroSumSubspace K 4 := by
  classical
  let E := LinearMap.ker (fourLinearMap (K := K))
  have hcard : Nat.card E = 16 := by
    let : Fintype E := Fintype.ofFinite E
    rw [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    change (underlyingFinset E).card = 16
    rw [p4_kernel_roots, Multiset.toFinset_card_of_nodup (nodup_roots p4_separable),
      ← hsplit.natDegree_eq_card_roots, p4_degree]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
  rw [Nat.card_zmod] at hpow
  have hr : Module.finrank (ZMod 2) E = 4 := by
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    calc
      2 ^ Module.finrank (ZMod 2) E = Nat.card E := hpow.symm
      _ = 16 := hcard
      _ = 2 ^ 4 := by norm_num
  refine ⟨E, hr, ?_⟩
  apply (zeroSum_iff_coeff_two E).mpr
  rw [p4_kernel_product hsplit]
  exact p4_coeff_two

theorem hasZeroSumSubspace_four_of_seven_dvd {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] [DecidableEq K] (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 7 ∣ n) : HasZeroSumSubspace K 4 := by
  exact hasZeroSumSubspace_four_of_polynomial4_splits (linearizedP4_splits_of_seven_dvd n hn hd)

theorem oddCarletConjecture_iff_four_and_five_7_31_remaining :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∧ ¬ 7 ∣ n ∨ k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_four_and_five_31_remaining.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with hk | ⟨hk, h5, h21, h31⟩
    · by_cases h7 : 7 ∣ n
      · subst k
        exact hasZeroSumSubspace_four_of_seven_dvd n (finrank_eq_of_card n hcard) h7
      · exact h n k hn (Or.inl ⟨hk, h7⟩) hb K hcard
    · exact h n k hn (Or.inr ⟨hk, h5, h21, h31⟩) hb K hcard

#print axioms hasZeroSumSubspace_four_of_seven_dvd
#print axioms oddCarletConjecture_iff_four_and_five_7_31_remaining
end Carlet
