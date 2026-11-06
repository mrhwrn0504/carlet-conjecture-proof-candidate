import Carlet.Frobenius21
noncomputable section
open Polynomial
namespace Carlet
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
local instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def fiveLinearMap : K →ₗ[ZMod 2] K where
  toFun := linearizedP
  map_add' := by
    intro x y
    simp only [linearizedP, add_pow_char_pow]
    ring
  map_smul' := by
    intro a x
    fin_cases a
    · change linearizedP ((0 : ZMod 2) • x) = (0 : ZMod 2) • linearizedP x
      simp [linearizedP]
    · change linearizedP ((1 : ZMod 2) • x) = (1 : ZMod 2) • linearizedP x
      simp

omit [Fintype K] [DecidableEq K] in
theorem five_poly_eval (x : K) : (linearizedP (X : K[X])).eval x = fiveLinearMap x := by
  simp [linearizedP, fiveLinearMap]

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem five_poly_monic : (linearizedP (X : K[X])).Monic := by
  unfold linearizedP
  norm_num only
  monicity <;> norm_num

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem five_poly_coeff_two : (linearizedP (X : K[X])).coeff 2 = 0 := by
  simp [linearizedP, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]

omit [Fintype K] [DecidableEq K] in
theorem five_poly_derivative : derivative (linearizedP (X : K[X])) = 1 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h31 : (31 : K) + 1 = 0 := by linear_combination (16 : K) * htwo
  have h15 : (15 : K) + 1 = 0 := by linear_combination (8 : K) * htwo
  have hc31 : C (31 : K) + 1 = 0 := by rw [← C_1, ← map_add, h31, map_zero]
  have hc15 : C (15 : K) + 1 = 0 := by rw [← C_1, ← map_add, h15, map_zero]
  simp [linearizedP, hc31, hc15]

omit [Fintype K] [DecidableEq K] in
theorem five_poly_separable : (linearizedP (X : K[X])).Separable := by
  rw [separable_def, five_poly_derivative]
  exact isCoprime_one_right

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem five_poly_degree : (linearizedP (X : K[X])).natDegree = 32 := by
  unfold linearizedP
  norm_num only
  compute_degree!

theorem five_kernel_roots :
    underlyingFinset (LinearMap.ker (fiveLinearMap (K := K))) =
      (linearizedP (X : K[X])).roots.toFinset := by
  classical
  ext x
  simp only [mem_underlyingFinset, LinearMap.mem_ker, Multiset.mem_toFinset,
    Polynomial.mem_roots (five_poly_monic (K := K)).ne_zero, Polynomial.IsRoot, five_poly_eval]

theorem five_kernel_card (hsplit : (linearizedP (X : K[X])).Splits) :
    Nat.card (LinearMap.ker (fiveLinearMap (K := K))) = 32 := by
  classical
  let : Fintype (LinearMap.ker (fiveLinearMap (K := K))) := Fintype.ofFinite _
  rw [← Fintype.card_eq_nat_card, Fintype.card_subtype]
  change (underlyingFinset (LinearMap.ker (fiveLinearMap (K := K)))).card = 32
  rw [five_kernel_roots, Multiset.toFinset_card_of_nodup (nodup_roots (five_poly_separable (K := K))),
    ← hsplit.natDegree_eq_card_roots, five_poly_degree]

theorem five_kernel_product (hsplit : (linearizedP (X : K[X])).Splits) :
    rootProduct (underlyingFinset (LinearMap.ker (fiveLinearMap (K := K)))) =
      linearizedP (X : K[X]) := by
  classical
  rw [five_kernel_roots]
  calc
    _ = ((linearizedP (X : K[X])).roots.map (fun x => X - C x)).prod := by
      unfold rootProduct
      simp only [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr
        (nodup_roots (five_poly_separable (K := K))), CharTwo.sub_eq_add]
    _ = _ := (hsplit.eq_prod_roots_of_monic (five_poly_monic (K := K))).symm

theorem hasZeroSumSubspace_five_of_polynomial_splits
    (hsplit : (linearizedP (X : K[X])).Splits) : HasZeroSumSubspace K 5 := by
  classical
  let E := LinearMap.ker (fiveLinearMap (K := K))
  have hcard : Nat.card E = 32 := five_kernel_card hsplit
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
  rw [five_kernel_product hsplit]
  exact five_poly_coeff_two

#print axioms hasZeroSumSubspace_five_of_polynomial_splits
#print axioms five_kernel_product
#print axioms five_kernel_card
#print axioms five_kernel_roots
#print axioms five_poly_degree
#print axioms five_poly_separable
#print axioms five_poly_monic
#print axioms five_poly_coeff_two
end Carlet
