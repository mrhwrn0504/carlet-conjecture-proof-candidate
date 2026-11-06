import Carlet.K5NormOneTracePlaneProbe
import Carlet.LowDimensionalK5Assembly
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace Carlet

variable {K : Type} [Field K] [Fintype K]
  [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- A rank-three seed with nonzero X⁴ coefficient extends to a rank-five
    zero-sum subspace, using an F₂-norm-one pair and the elliptic bound. -/
theorem k5_of_rankThree_coeffFour_nonzero (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K = n)
    (hq : 65536 ≤ Fintype.card K) (U : Submodule (ZMod 2) K)
    (hU : Module.finrank (ZMod 2) U = 3)
    (hb : (rootProduct (underlyingFinset U)).coeff 4 ≠ 0) :
    HasZeroSumSubspace K 5 := by
  let b : K := (rootProduct (underlyingFinset U)).coeff 4
  let c : K := b ^ 2
  have hc : c ≠ 0 := pow_ne_zero 2 hb
  obtain ⟨p, hgood, ha0, ha1⟩ :=
    k5NormOneTracePlane_exists_nondegenerate n hn hfinrank U c hU hc hq
  let a : K := p.val.1
  let u : K := p.val.2
  have htracea : ∀ w ∈ k5NormOneTracePlane U c,
      Algebra.trace (ZMod 2) K (w * a) = 0 := by
    intro w hw
    have hu := hgood.1 w hw
    have hau := hgood.2 w hw
    have hsplit : Algebra.trace (ZMod 2) K (w * (a + u)) =
        Algebra.trace (ZMod 2) K (w * a) + Algebra.trace (ZMod 2) K (w * u) := by
      rw [mul_add, map_add]
    rw [hau, hu] at hsplit
    simpa using hsplit.symm
  obtain ⟨x, hx⟩ := k5NormOneTracePlane_preimage U c a hc htracea
  obtain ⟨y, hy⟩ := k5NormOneTracePlane_preimage U c u hc hgood.1
  have hxout : x ∉ U := by
    intro hxU
    have hzero := (subspacePolynomial_eval_eq_zero_iff U x).mpr hxU
    rw [hzero] at hx
    exact (mul_ne_zero hc ha0) hx.symm
  let V := U ⊔ Submodule.span (ZMod 2) ({x} : Set K)
  have hV : Module.finrank (ZMod 2) V = 4 := by
    dsimp [V]
    rw [extension_finrank U x hxout, hU]
  have htop : (rootProduct (underlyingFinset U)).coeff 8 = 1 := by
    have hdeg : (rootProduct (underlyingFinset U)).natDegree = 8 := by
      rw [rootProduct_natDegree, underlyingFinset_card_pow, hU]
      norm_num
    rw [← hdeg]
    exact (rootProduct_monic _).coeff_natDegree
  have hcoeff : (rootProduct (underlyingFinset V)).coeff 8 = c * (1 + a) := by
    have hrec := rootProduct_sup_step_coeff_pow U x hxout 2
    calc
      _ = b ^ 2 + (rootProduct (underlyingFinset U)).eval x *
          (rootProduct (underlyingFinset U)).coeff 8 := by
        simpa [V, b] using hrec
      _ = c * (1 + a) := by
        rw [hx, htop]
        dsimp [c]
        ring
  have h1a : 1 + a ≠ 0 := by
    intro h
    have ha : a = 1 := by
      simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp h).symm
    exact ha1 ha
  have hcoeff_ne : (rootProduct (underlyingFinset V)).coeff 8 ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hc h1a
  have hnorm : a ^ 2 + a * u + u ^ 2 = 1 := p.property
  have hnorm' : u ^ 2 + a * u = 1 + a ^ 2 := by
    have hsum := congrArg (fun z : K => z + a ^ 2) hnorm
    have hcancel : a ^ 2 + a ^ 2 = 0 := CharTwo.add_self_eq_zero (a ^ 2)
    have hinner : a ^ 2 + (a ^ 2 + u ^ 2) = u ^ 2 := by
      calc
        _ = (a ^ 2 + a ^ 2) + u ^ 2 := by abel
        _ = u ^ 2 := by rw [hcancel, zero_add]
    calc
      u ^ 2 + a * u = a * u + u ^ 2 := by ac_rfl
      _ = a * u + (a ^ 2 + (a ^ 2 + u ^ 2)) := by rw [hinner]
      _ = a ^ 2 + a * u + u ^ 2 + a ^ 2 := by abel
      _ = 1 + a ^ 2 := hsum
  have heval : (rootProduct (underlyingFinset V)).eval y =
      c ^ 2 * (u ^ 2 + a * u) := by
    dsimp [V]
    rw [subspacePolynomial_extension U x hxout]
    simp only [Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [hx, hy]
    ring
  have hsquare : (1 + a) ^ 2 = 1 + a ^ 2 := by
    simpa using (add_pow_char (1 : K) a 2)
  have htarget : (rootProduct (underlyingFinset V)).eval y =
      ((rootProduct (underlyingFinset V)).coeff 8) ^ 2 := by
    calc
      _ = c ^ 2 * (u ^ 2 + a * u) := heval
      _ = c ^ 2 * (1 + a ^ 2) := by rw [hnorm']
      _ = (c * (1 + a)) ^ 2 := by rw [mul_pow, hsquare]
      _ = _ := by rw [hcoeff]
  exact rankFour_k5_of_nonzero_target_in_range V hV hcoeff_ne ⟨y, htarget⟩

theorem hasZeroSumSubspace_five_of_odd_card_ge17
    (n : ℕ) (hn : Odd n) (hmin : 17 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) : HasZeroSumSubspace K 5 := by
  have hfinrank := finrank_eq_of_card n hcard
  have hq : 65536 ≤ Fintype.card K := by
    rw [hcard]
    calc
      65536 = 2 ^ 16 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨U, hU, hb⟩ :=
    exists_rankThree_coeffFour_nonzero_of_odd_card n hn (by omega) hcard
  exact k5_of_rankThree_coeffFour_nonzero n hn hfinrank hq U hU hb

/-- The full admissible odd-degree k=5 family, including its small boundary. -/
theorem hasZeroSumSubspace_five_of_odd_card
    (n : ℕ) (hn : Odd n) (hmin : 9 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) : HasZeroSumSubspace K 5 := by
  by_cases hsmall : n < 17
  · exact hasZeroSumSubspace_five_of_odd_card_lt37 n hn hmin (by omega) K hcard
  · exact hasZeroSumSubspace_five_of_odd_card_ge17 n hn (by omega) hcard

/-- The original quantified proposition, discharged without extra hypotheses. -/
theorem oddCarletConjecture_normOne : OddCarletConjecture := by
  apply oddCarletConjecture_of_five
  intro n hn hmin K _ _ _ hcard
  classical
  exact hasZeroSumSubspace_five_of_odd_card n hn (by omega) hcard

#print axioms k5_of_rankThree_coeffFour_nonzero
#print axioms hasZeroSumSubspace_five_of_odd_card_ge17
#print axioms hasZeroSumSubspace_five_of_odd_card
#print axioms oddCarletConjecture_normOne
end Carlet
