import HasseWeil.HasseBound
import Carlet.SmallProbability
import Carlet.ArtinSchreier
import Carlet.ProbabilityEnergy

noncomputable section
open scoped BigOperators

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def kloostermanCurve : WeierstrassCurve K := ⟨1, 0, 0, 0, 1⟩

omit [Fintype K] [DecidableEq K] in
theorem kloostermanCurve_discriminant : (kloostermanCurve (K := K)).Δ = 1 := by
  rw [WeierstrassCurve.Δ_of_char_two, WeierstrassCurve.b₈_of_char_two]
  simp [kloostermanCurve]

instance : (kloostermanCurve (K := K)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, kloostermanCurve_discriminant]
  exact isUnit_one

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem kloostermanCurve_equation (x y : K) :
    (kloostermanCurve (K := K)).toAffine.Equation x y ↔ y^2 + x*y = x^3 + 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [kloostermanCurve, WeierstrassCurve.toAffine]

def kloostermanCurvePairs := {xy : K × K // xy.2^2 + xy.1*xy.2 = xy.1^3 + 1}

instance : Fintype (kloostermanCurvePairs (K := K)) := by
  classical
  unfold kloostermanCurvePairs
  exact Fintype.ofFinite _

def kloostermanCurvePointEquiv : (kloostermanCurve (K := K)).toAffine.Point ≃
    Option (kloostermanCurvePairs (K := K)) :=
  (kloostermanCurve (K := K)).toAffine.nonsingularPointEquiv.trans
    (Equiv.optionCongr (Equiv.subtypeEquivProp (by
      funext xy
      apply propext
      rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, kloostermanCurve_equation])))

instance : Fintype (kloostermanCurve (K := K)).toAffine.Point :=
  Fintype.ofEquiv (Option (kloostermanCurvePairs (K := K))) kloostermanCurvePointEquiv.symm

omit [DecidableEq K] in
theorem kloostermanCurve_pointCount :
    HasseWeil.pointCount (kloostermanCurve (K := K)).toAffine =
      Fintype.card (kloostermanCurvePairs (K := K)) + 1 := by
  rw [HasseWeil.pointCount, Fintype.card_congr (kloostermanCurvePointEquiv (K := K))]
  simp

def kloostermanCurveFibers : kloostermanCurvePairs (K := K) ≃
    Σ x : K, {y : K // y^2 + x*y = x^3 + 1} where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨⟨p.1, p.2.val⟩, p.2.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

omit [Algebra (ZMod 2) K] in
theorem kloostermanCurve_pairs_card :
    Fintype.card (kloostermanCurvePairs (K := K)) =
      ∑ x : K, Fintype.card {y : K // y^2 + x*y = x^3 + 1} := by
  classical
  rw [Fintype.card_congr (kloostermanCurveFibers (K := K)), Fintype.card_sigma]

def artinSchreierFiberEquivKer (c y₀ : K) (hy₀ : artinSchreier y₀ = c) :
    {y : K // y^2 + y = c} ≃ LinearMap.ker (artinSchreier (K := K)) where
  toFun y := ⟨y.val - y₀, by
    rw [LinearMap.mem_ker, map_sub, hy₀]
    change y.val^2 + y.val - c = 0
    rw [y.property, sub_self]⟩
  invFun z := ⟨z.val + y₀, by
    change artinSchreier (z.val + y₀) = c
    rw [map_add, LinearMap.mem_ker.mp z.property, zero_add, hy₀]⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

theorem artinSchreier_fiber_card (c : K) :
    (Fintype.card {y : K // y^2 + y = c} : ℝ) = 1 + traceCharacter (K := K) c := by
  classical
  by_cases hc : Algebra.trace (ZMod 2) K c = 0
  · have hc' : c ∈ LinearMap.range (artinSchreier (K := K)) := by
      rw [artinSchreier_range]
      exact hc
    obtain ⟨y₀, hy₀⟩ := hc'
    have hcard : Fintype.card (LinearMap.ker (artinSchreier (K := K))) = 2 := by
      rw [artinSchreier_ker, ← Nat.card_eq_fintype_card]
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Submodule.span (ZMod 2) ({1} : Set K)),
        finrank_span_singleton (one_ne_zero : (1 : K) ≠ 0)]
      simp [ZMod.card, Nat.card_eq_fintype_card]
    rw [Fintype.card_congr (artinSchreierFiberEquivKer c y₀ hy₀), hcard]
    rw [(traceCharacter_eq_one_iff c).mpr hc]
    norm_num
  · have hempty : IsEmpty {y : K // y^2 + y = c} := ⟨fun y => by
      apply hc
      have hy : artinSchreier y.val = c := by simpa [artinSchreier_apply] using y.property
      have hmem : c ∈ LinearMap.range (artinSchreier (K := K)) := ⟨y.val, hy⟩
      rw [artinSchreier_range] at hmem
      exact hmem⟩
    let _ : IsEmpty {y : K // y^2 + y = c} := hempty
    have hcard : Fintype.card {y : K // y^2 + y = c} = 0 := Fintype.card_eq_zero
    have hψ : traceCharacter (K := K) c = -1 := by
      change (if Algebra.trace (ZMod 2) K c = 0 then (1 : ℝ) else -1) = -1
      simp [hc]
    rw [hcard, hψ]
    norm_num

def kloostermanFiberEquiv (x : K) (hx : x ≠ 0) :
    {y : K // y^2 + x*y = x^3 + 1} ≃
      {t : K // t^2 + t = x + (x⁻¹)^2} where
  toFun y := ⟨y.val / x, by
    have hy := y.property
    field_simp [hx]
    linear_combination hy⟩
  invFun t := ⟨x * t.val, by
    have ht := t.property
    field_simp [hx] at ht
    linear_combination ht⟩
  left_inv y := by apply Subtype.ext; field_simp
  right_inv t := by apply Subtype.ext; simp [hx]

theorem kloostermanCurve_nonzero_fiber_card (x : K) (hx : x ≠ 0) :
    (Fintype.card {y : K // y^2 + x*y = x^3 + 1} : ℝ) =
      1 + traceCharacter (K := K) (x + x⁻¹) := by
  rw [Fintype.card_congr (kloostermanFiberEquiv x hx), artinSchreier_fiber_card]
  congr 1
  change binaryCharacter (Algebra.trace (ZMod 2) K (x + (x⁻¹)^2)) =
    binaryCharacter (Algebra.trace (ZMod 2) K (x + x⁻¹))
  apply congrArg binaryCharacter
  rw [map_add, map_add, trace_square]

theorem kloostermanCurve_zero_fiber_card :
    Fintype.card {y : K // y^2 + (0 : K)*y = (0 : K)^3 + 1} = 1 := by
  classical
  let _ : Unique {y : K // y^2 + (0 : K)*y = (0 : K)^3 + 1} := {
    default := ⟨1, by simp⟩
    uniq := fun y => by
      apply Subtype.ext
      have hy : y.val^2 = (1 : K)^2 := by simpa using y.property
      have h := sq_eq_sq_iff_eq_or_eq_neg.mp hy
      simpa only [CharTwo.neg_eq, or_self] using h
  }
  exact Fintype.card_unique

def binaryKloostermanSum : ℝ :=
  ∑ x ∈ Transfer.nonzeroElements (K := K), traceCharacter (K := K) (x + x⁻¹)

theorem kloostermanCurve_pointCount_eq :
    (HasseWeil.pointCount (kloostermanCurve (K := K)).toAffine : ℝ) =
      (Fintype.card K : ℝ) + 1 + binaryKloostermanSum (K := K) := by
  classical
  rw [kloostermanCurve_pointCount, kloostermanCurve_pairs_card]
  push_cast
  have hz : (Fintype.card {y : K // y^2 + (0 : K)*y = (0 : K)^3 + 1} : ℝ) = 1 := by
    exact_mod_cast (kloostermanCurve_zero_fiber_card (K := K))
  have hcount : ((Transfer.nonzeroElements (K := K)).card : ℝ) + 1 = Fintype.card K := by
    have hc : (Transfer.nonzeroElements (K := K)).card + 1 = Fintype.card K := by
      simpa [Transfer.nonzeroElements] using
        (Finset.card_erase_add_one (Finset.mem_univ (0 : K)))
    exact_mod_cast hc
  have hsum :
      (∑ x ∈ Transfer.nonzeroElements (K := K),
        (Fintype.card {y : K // y^2 + x*y = x^3 + 1} : ℝ)) =
        (Transfer.nonzeroElements (K := K)).card + binaryKloostermanSum (K := K) := by
    calc
      _ = ∑ x ∈ Transfer.nonzeroElements (K := K),
          (1 + traceCharacter (K := K) (x + x⁻¹)) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 : x ≠ 0 := by simpa [Transfer.nonzeroElements] using hx
        exact kloostermanCurve_nonzero_fiber_card x hx0
      _ = _ := by simp [Finset.sum_add_distrib, binaryKloostermanSum]
  have hset : insert (0 : K) (Transfer.nonzeroElements (K := K)) = Finset.univ := by
    ext x
    by_cases hx : x = 0 <;> simp [Transfer.nonzeroElements, hx]
  have hnot : (0 : K) ∉ Transfer.nonzeroElements (K := K) := by
    simp [Transfer.nonzeroElements]
  have hsplit' := Finset.sum_insert hnot
    (f := fun x => (Fintype.card {y : K // y^2 + x*y = x^3 + 1} : ℝ))
  rw [hset] at hsplit'
  rw [hsum, hz] at hsplit'
  linarith

theorem binaryKloostermanSum_bound :
    |binaryKloostermanSum (K := K)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ) := by
  have h := HasseWeil.WeilPairing.hasse_bound (kloostermanCurve (K := K))
  have heq :
      (HasseWeil.pointCount (kloostermanCurve (K := K)).toAffine : ℝ) -
        (Fintype.card K : ℝ) - 1 = binaryKloostermanSum (K := K) := by
    linarith [kloostermanCurve_pointCount_eq (K := K)]
  rwa [heq] at h

theorem weighted_probability_two (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (hn7 : 7 ≤ n) :
    ((Fintype.card K : ℝ) - 2) *
      (∑ v ∈ Transfer.nonzeroElements (K := K),
        traceCharacter (K := K) (v⁻¹) * containingOneCoefficientProbability (K := K) 2 v) =
      1 - binaryKloostermanSum (K := K) := by
  classical
  have hqnat : 128 ≤ Fintype.card K := by
    rw [field_card_eq_pow_finrank_local n hn]
    exact le_trans (by norm_num : 128 ≤ 2^7) (Nat.pow_le_pow_right (by omega) hn7)
  have hq : (128 : ℝ) ≤ Fintype.card K := by exact_mod_cast hqnat
  have hden : (Fintype.card K : ℝ) - 2 ≠ 0 := by linarith
  have hψ := traceCharacter_one_of_odd_finrank (K := K) n hn hodd
  have hp (v : K) : ((Fintype.card K : ℝ) - 2) *
      containingOneCoefficientProbability (K := K) 2 v =
        1 - traceCharacter (K := K) v - (if v = 1 then 2 else 0) := by
    rw [containingOne_probability_two_dim n hn (by omega)]
    by_cases hv : v = 1
    · subst v; simp [hψ]; norm_num
    · rw [if_neg hv, if_neg hv]
      rw [AddChar.map_add_eq_mul, hψ]
      field_simp
      ring
  have ha : (∑ v ∈ Transfer.nonzeroElements (K := K),
      traceCharacter (K := K) (v⁻¹)) = -1 := by
    simpa only [one_div] using
      (Transfer.sum_nonzero_char_div_left (traceCharacter (K := K))
        (traceCharacter_ne_zero (K := K)) 1 one_ne_zero)
  have hb : (∑ v ∈ Transfer.nonzeroElements (K := K),
      traceCharacter (K := K) (v⁻¹) * traceCharacter (K := K) v) =
      binaryKloostermanSum (K := K) := by
    unfold binaryKloostermanSum
    apply Finset.sum_congr rfl
    intro v hv
    rw [← AddChar.map_add_eq_mul, add_comm]
  have hc : (∑ v ∈ Transfer.nonzeroElements (K := K),
      traceCharacter (K := K) (v⁻¹) * (if v = 1 then (2 : ℝ) else 0)) = -2 := by
    rw [Finset.sum_eq_single 1]
    · simp [hψ]
    · intro v hv hv1; simp [hv1]
    · simp [Transfer.nonzeroElements]
  calc
    _ = ∑ v ∈ Transfer.nonzeroElements (K := K),
        (traceCharacter (K := K) (v⁻¹) -
          traceCharacter (K := K) (v⁻¹) * traceCharacter (K := K) v -
          traceCharacter (K := K) (v⁻¹) * (if v = 1 then (2 : ℝ) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      calc
        _ = traceCharacter (K := K) (v⁻¹) *
            (((Fintype.card K : ℝ) - 2) * containingOneCoefficientProbability (K := K) 2 v) := by ring
        _ = _ := by rw [hp v]; ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ha, hb, hc]; ring

theorem probability_three_formula (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (hn7 : 7 ≤ n) :
    ((Fintype.card K : ℝ) - 2) * ((Fintype.card K : ℝ) - 4) *
      containingOneCoefficientProbability (K := K) 3 0 =
        (Fintype.card K : ℝ) + 1 - 3 * binaryKloostermanSum (K := K) := by
  have h := containingOne_probability_three_zero (K := K) n hn (by omega) hodd
  have hw := weighted_probability_two (K := K) n hn hodd hn7
  nlinarith

theorem probability_three_positive (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (hn7 : 7 ≤ n) :
    0 < containingOneCoefficientProbability (K := K) 3 0 := by
  have hqnat : 128 ≤ Fintype.card K := by
    rw [field_card_eq_pow_finrank_local n hn]
    exact le_trans (by norm_num : 128 ≤ 2^7) (Nat.pow_le_pow_right (by omega) hn7)
  have hq : (128 : ℝ) ≤ Fintype.card K := by exact_mod_cast hqnat
  have hs := Real.sqrt_nonneg (Fintype.card K : ℝ)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card K by positivity)
  have hs8 : 8 < Real.sqrt (Fintype.card K : ℝ) := by nlinarith
  have hk := binaryKloostermanSum_bound (K := K)
  have hk' := le_trans (le_abs_self (binaryKloostermanSum (K := K))) hk
  have hrhs : 0 < (Fintype.card K : ℝ) + 1 - 3 * binaryKloostermanSum (K := K) := by
    nlinarith
  have hf := probability_three_formula (K := K) n hn hodd hn7
  have hp : 0 < ((Fintype.card K : ℝ) - 2) * ((Fintype.card K : ℝ) - 4) :=
    mul_pos (by linarith) (by linarith)
  have hpositive : 0 < (((Fintype.card K : ℝ) - 2) * ((Fintype.card K : ℝ) - 4)) *
      containingOneCoefficientProbability (K := K) 3 0 := by linarith
  exact (mul_pos_iff_of_pos_left hp).mp hpositive

theorem hasZeroSumSubspace_three (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (hn7 : 7 ≤ n) :
    HasZeroSumSubspace K 3 := by
  have hprob := probability_three_positive (K := K) n hn hodd hn7
  obtain ⟨H⟩ := containingOneCoefficientFiber_nonempty_of_probability_pos
    (K := K) n 3 hn (by omega) (by omega) hprob
  let E : {E : Submodule (ZMod 2) K //
      Module.finrank (ZMod 2) E = 3 ∧ nextFrobeniusCoefficient E = 0} :=
    ⟨H.val, H.property.1, H.property.2.2⟩
  let Z := nextCoefficientZeroEquivZeroSum (K := K) 3 (by omega) E
  exact ⟨Z.val, Z.property.1, Z.property.2⟩

#print axioms hasZeroSumSubspace_three
#print axioms probability_three_positive
#print axioms weighted_probability_two
#print axioms kloostermanCurve_discriminant
#print axioms kloostermanCurve_equation
#print axioms kloostermanCurve_pointCount
#print axioms kloostermanCurve_pairs_card
#print axioms artinSchreier_fiber_card
#print axioms kloostermanCurve_nonzero_fiber_card
#print axioms kloostermanCurve_zero_fiber_card
#print axioms kloostermanCurve_pointCount_eq
#print axioms binaryKloostermanSum_bound

end Carlet
