import Carlet.FiveDimension21

noncomputable section

open Polynomial

namespace Carlet

/-- The Frobenius-invariant linearized polynomial associated with
`T^5 + T^2 + 1`. -/
def linearizedP31 {R : Type*} [CommRing R] (x : R) : R :=
  x^(2^5 : ℕ) + x^(2^2 : ℕ) + x

def linearizedQ31 {R : Type*} [CommRing R] (y : R) : R :=
  y^(2^26 : ℕ) + y^(2^23 : ℕ) + y^(2^21 : ℕ) + y^(2^20 : ℕ) +
  y^(2^17 : ℕ) + y^(2^16 : ℕ) + y^(2^15 : ℕ) + y^(2^14 : ℕ) +
  y^(2^13 : ℕ) + y^(2^9 : ℕ) + y^(2^8 : ℕ) + y^(2^6 : ℕ) +
  y^(2^5 : ℕ) + y^(2^4 : ℕ) + y^(2^2 : ℕ) + y

theorem linearizedQ31_dvd {R : Type*} [CommRing R] (y : R) :
    y ∣ linearizedQ31 y := by
  unfold linearizedQ31
  repeat' apply dvd_add
  all_goals first | exact dvd_refl y | exact dvd_pow_self y (by norm_num)

theorem linearizedPQ31 {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    linearizedQ31 (linearizedP31 x) = x^(2^31 : ℕ) + x := by
  unfold linearizedP31 linearizedQ31
  simp only [add_pow_char_pow, ← pow_mul]
  ring_nf
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simp [htwo]

theorem linearizedP31_dvd {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    linearizedP31 x ∣ x^(2^31 : ℕ) + x := by
  rw [← linearizedPQ31 x]
  exact linearizedQ31_dvd _

/-- Keep the large Frobenius exponent opaque while transporting it to the
cardinality exponent used by the finite-field splitting theorem. -/
theorem linearizedP31_dvd_exp {R : Type*} [CommRing R] [CharP R 2]
    (x : R) (m : ℕ) (hm : m = 2^31) : linearizedP31 x ∣ x^m + x := by
  have heq : x^m + x = x^(2^31 : ℕ) + x := by rw [hm]
  rw [heq]
  exact linearizedP31_dvd x

theorem linearizedP31_splits_of_card {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hc : Fintype.card K = 2^31) :
    (linearizedP31 (X : K[X])).Splits := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  apply split_of_card_divides
  exact linearizedP31_dvd_exp (X : K[X]) (Fintype.card K) hc

theorem linearizedP31_splits_of_31_dvd {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (hd : 31 ∣ n) : (linearizedP31 (X : K[X])).Splits := by
  classical
  let L := GaloisField 2 31
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 31 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 2^31 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
  have hs : (linearizedP31 (X : L[X])).Splits := linearizedP31_splits_of_card hc
  have hdim : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, hn] using hd
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdim
  have hm := hs.map f.toRingHom
  simpa only [linearizedP31, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X] using hm

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def fiveLinearMap31 : K →ₗ[ZMod 2] K where
  toFun := linearizedP31
  map_add' := by
    intro x y
    simp only [linearizedP31, add_pow_char_pow]
    ring
  map_smul' := by
    intro a x
    fin_cases a
    · change linearizedP31 ((0 : ZMod 2) • x) = (0 : ZMod 2) • linearizedP31 x
      simp [linearizedP31]
    · change linearizedP31 ((1 : ZMod 2) • x) = (1 : ZMod 2) • linearizedP31 x
      simp

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem p31_monic : (linearizedP31 (X : K[X])).Monic := by
  unfold linearizedP31
  norm_num only
  monicity <;> norm_num

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem p31_coeff_two : (linearizedP31 (X : K[X])).coeff 2 = 0 := by
  simp [linearizedP31, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]

omit [Fintype K] [DecidableEq K] in
theorem p31_derivative : derivative (linearizedP31 (X : K[X])) = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h31 : (31 : K) + 1 = 0 := by linear_combination (16 : K) * htwo
  have h3 : (3 : K) + 1 = 0 := by linear_combination (2 : K) * htwo
  have hc31 : C (31 : K) + 1 = 0 := by rw [← C_1, ← map_add, h31, map_zero]
  have hc3 : C (3 : K) + 1 = 0 := by rw [← C_1, ← map_add, h3, map_zero]
  simp [linearizedP31, hc31, hc3]

omit [Fintype K] [DecidableEq K] in
theorem p31_separable : (linearizedP31 (X : K[X])).Separable := by
  rw [separable_def, p31_derivative]
  exact isCoprime_one_right

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem p31_degree : (linearizedP31 (X : K[X])).natDegree = 32 := by
  unfold linearizedP31
  norm_num only
  compute_degree!

theorem p31_kernel_roots :
    underlyingFinset (LinearMap.ker (fiveLinearMap31 (K := K))) =
      (linearizedP31 (X : K[X])).roots.toFinset := by
  classical
  ext x
  simp only [mem_underlyingFinset, LinearMap.mem_ker, Multiset.mem_toFinset,
    Polynomial.mem_roots p31_monic.ne_zero, Polynomial.IsRoot]
  simp [fiveLinearMap31, linearizedP31]

theorem p31_kernel_product (hsplit : (linearizedP31 (X : K[X])).Splits) :
    rootProduct (underlyingFinset (LinearMap.ker (fiveLinearMap31 (K := K)))) =
      linearizedP31 (X : K[X]) := by
  classical
  rw [p31_kernel_roots]
  calc
    _ = ((linearizedP31 (X : K[X])).roots.map (fun x => X - C x)).prod := by
      unfold rootProduct
      simp only [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr
        (nodup_roots p31_separable), CharTwo.sub_eq_add]
    _ = _ := (hsplit.eq_prod_roots_of_monic p31_monic).symm

theorem hasZeroSumSubspace_five_of_polynomial31_splits
    (hsplit : (linearizedP31 (X : K[X])).Splits) : HasZeroSumSubspace K 5 := by
  classical
  let E := LinearMap.ker (fiveLinearMap31 (K := K))
  have hcard : Nat.card E = 32 := by
    let : Fintype E := Fintype.ofFinite E
    rw [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    change (underlyingFinset E).card = 32
    rw [p31_kernel_roots, Multiset.toFinset_card_of_nodup (nodup_roots p31_separable),
      ← hsplit.natDegree_eq_card_roots, p31_degree]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
  rw [Nat.card_zmod] at hpow
  have hr : Module.finrank (ZMod 2) E = 5 := by
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    calc
      2 ^ Module.finrank (ZMod 2) E = Nat.card E := hpow.symm
      _ = 32 := hcard
      _ = 2 ^ 5 := by norm_num
  refine ⟨E, hr, ?_⟩
  apply (zeroSum_iff_coeff_two E).mpr
  rw [p31_kernel_product hsplit]
  exact p31_coeff_two

theorem hasZeroSumSubspace_five_of_31_dvd (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hd : 31 ∣ n) : HasZeroSumSubspace K 5 := by
  exact hasZeroSumSubspace_five_of_polynomial31_splits
    (linearizedP31_splits_of_31_dvd n hn hd)

theorem oddCarletConjecture_iff_four_and_five_31_remaining :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n →
        (k = 4 ∨ k = 5 ∧ ¬ 5 ∣ n ∧ ¬ 21 ∣ n ∧ ¬ 31 ∣ n) →
        2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk hb K _ _ _ hcard
    exact h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_four_and_five_remaining.mpr
    intro n k hn hk hb K _ _ _ hcard
    rcases hk with hk | ⟨hk, h5, h21⟩
    · exact h n k hn (Or.inl hk) hb K hcard
    · by_cases h31 : 31 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_31_dvd n (finrank_eq_of_card n hcard) h31
      · exact h n k hn (Or.inr ⟨hk, h5, h21, h31⟩) hb K hcard

#print axioms linearizedP31_splits_of_31_dvd
#print axioms hasZeroSumSubspace_five_of_31_dvd
#print axioms oddCarletConjecture_iff_four_and_five_31_remaining

end Carlet
