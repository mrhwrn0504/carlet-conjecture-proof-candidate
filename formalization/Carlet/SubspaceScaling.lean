import Carlet.DualSubspacePolynomial
import Mathlib.Algebra.Module.Equiv.Basic

noncomputable section

open Polynomial

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

def scalarEquiv (a : Kˣ) : K ≃ₗ[ZMod 2] K :=
  a.mulLeftLinearEquiv (ZMod 2) K

def scalarSubspace (E : Submodule (ZMod 2) K) (a : Kˣ) : Submodule (ZMod 2) K :=
  E.map (scalarEquiv a).toLinearMap

omit [Fintype K] [DecidableEq K] in
@[simp] theorem mem_scalarSubspace (E : Submodule (ZMod 2) K) (a : Kˣ) (y : K) :
    y ∈ scalarSubspace E a ↔ (a : K)⁻¹ * y ∈ E := by
  rw [scalarSubspace, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    change (a : K) * x = y at hxy
    rw [← hxy]
    have hmul : (a : K)⁻¹ * ((a : K) * x) = x := by field_simp
    rw [hmul]
    exact hx
  · intro hy
    refine ⟨(a : K)⁻¹ * y, hy, ?_⟩
    change (a : K) * ((a : K)⁻¹ * y) = y
    field_simp

omit [Fintype K] [DecidableEq K] in
theorem scalarSubspace_finrank (E : Submodule (ZMod 2) K) (a : Kˣ) :
    Module.finrank (ZMod 2) (scalarSubspace E a) = Module.finrank (ZMod 2) E := by
  exact (scalarEquiv a).finrank_map_eq E

omit [Fintype K] [DecidableEq K] in
def scalarSubspaceEquiv (a : Kˣ) :
    Submodule (ZMod 2) K ≃ Submodule (ZMod 2) K where
  toFun E := scalarSubspace E a
  invFun E := scalarSubspace E a⁻¹
  left_inv E := by
    ext x
    simp only [mem_scalarSubspace]
    constructor <;> intro hx
    · simpa [mul_assoc] using hx
    · simpa [mul_assoc] using hx
  right_inv E := by
    ext x
    simp only [mem_scalarSubspace]
    constructor <;> intro hx
    · simpa [mul_assoc] using hx
    · simpa [mul_assoc] using hx

private def scaledPolynomial (p : K[X]) (a : Kˣ) (N : ℕ) : K[X] :=
  C ((a : K)^N) * p.comp (C ((a : K)⁻¹) * X)

omit [DecidableEq K] in
theorem scalarSubspace_subspacePolynomial (E : Submodule (ZMod 2) K) (a : Kˣ) :
    scaledPolynomial (rootProduct (underlyingFinset E)) a
      (2^Module.finrank (ZMod 2) E) = rootProduct (underlyingFinset (scalarSubspace E a)) := by
  classical
  let p := rootProduct (underlyingFinset E)
  let N := 2^Module.finrank (ZMod 2) E
  have ha : (a : K) ≠ 0 := Units.ne_zero a
  have hq : (C ((a : K)⁻¹) * (X : K[X])).natDegree = 1 := by
    simp [ha]
  have hcompdeg :
      (p.comp (C ((a : K)⁻¹) * X)).natDegree = p.natDegree := by
    rw [natDegree_comp_eq_of_mul_ne_zero]
    · rw [hq, mul_one]
    · have hpc : (C ((a : K)⁻¹) * X).leadingCoeff = (a : K)⁻¹ := by
        rw [leadingCoeff_C_mul_X]
      rw [hpc]
      apply mul_ne_zero
      · have hpne : p ≠ 0 := by
          simpa [p] using (rootProduct_monic (underlyingFinset E)).ne_zero
        exact leadingCoeff_ne_zero.mpr hpne
      · exact pow_ne_zero _ (inv_ne_zero ha)
  have hpdeg : p.natDegree = N := by
    simp [p, N, subspacePolynomial_natDegree_pow]
  have hdeg : (scaledPolynomial p a N).natDegree = N := by
    rw [scaledPolynomial, natDegree_C_mul]
    · rw [hcompdeg, hpdeg]
    · exact pow_ne_zero _ ha
  have hmonic : (scaledPolynomial p a N).Monic := by
    unfold scaledPolynomial
    rw [mul_comm]
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    have hqne : (C ((a : K)⁻¹) * X).natDegree ≠ 0 := by rw [hq]; omega
    rw [leadingCoeff_comp hqne, leadingCoeff_C_mul_X, hpdeg]
    rw [(rootProduct_monic (underlyingFinset E)).leadingCoeff]
    simp only [one_mul]
    rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
  apply monic_eq_rootProduct
  · exact hmonic
  · rw [hdeg]
    rw [underlyingFinset_card_pow, scalarSubspace_finrank]
  · intro y hy
    change (C ((a : K)^N) * p.comp (C ((a : K)⁻¹) * X)).eval y = 0
    rw [eval_mul, eval_C, eval_comp]
    have hscale : ((a : K) ^ N) ≠ 0 := pow_ne_zero _ ha
    have hp : p.eval ((a : K)⁻¹ * y) = 0 ↔ (a : K)⁻¹ * y ∈ E := by
      change (rootProduct (underlyingFinset E)).eval ((a : K)⁻¹ * y) = 0 ↔ _
      exact subspacePolynomial_eval_eq_zero_iff E _
    simp only [eval_mul, eval_C, eval_X]
    rw [mul_eq_zero]
    simp [hscale, hp]
    exact (mem_scalarSubspace E a y).mp ((mem_underlyingFinset _ _).mp hy)

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem scaledPolynomial_coeff (p : K[X]) (a : Kˣ) (N i : ℕ) :
    (scaledPolynomial p a N).coeff i =
      (a : K)^N * (p.coeff i * ((a : K)⁻¹)^i) := by
  rw [scaledPolynomial, coeff_C_mul, comp_C_mul_X_coeff]

omit [DecidableEq K] in
theorem nextCoefficient_scalarSubspace (E : Submodule (ZMod 2) K) (a : Kˣ)
    (hd : 0 < Module.finrank (ZMod 2) E) :
    nextFrobeniusCoefficient (scalarSubspace E a) =
      (a : K)^(2^(Module.finrank (ZMod 2) E-1)) * nextFrobeniusCoefficient E := by
  classical
  let d := Module.finrank (ZMod 2) E
  have hexp : 2^d = 2^(d-1) + 2^(d-1) := by
    calc
      2^d = 2^(d-1+1) := by congr 1; omega
      _ = 2^(d-1)*2 := by rw [pow_succ]
      _ = 2^(d-1)+2^(d-1) := by rw [Nat.mul_comm, two_mul]
  rw [nextFrobeniusCoefficient, scalarSubspace_finrank E a]
  change (rootProduct (underlyingFinset (scalarSubspace E a))).coeff (2^(d-1)) =
    (a : K)^(2^(d-1)) * (rootProduct (underlyingFinset E)).coeff (2^(d-1))
  rw [← scalarSubspace_subspacePolynomial E a, scaledPolynomial_coeff]
  change (a : K)^(2^d) *
    ((rootProduct (underlyingFinset E)).coeff (2^(d-1)) *
      ((a : K)⁻¹)^(2^(d-1))) = _
  rw [hexp, pow_add]
  have ha : (a : K) ≠ 0 := Units.ne_zero a
  calc
    (a : K)^(2^(d-1)) * (a : K)^(2^(d-1)) *
        ((rootProduct (underlyingFinset E)).coeff (2^(d-1)) *
          ((a : K)⁻¹)^(2^(d-1))) =
      (a : K)^(2^(d-1)) * ((rootProduct (underlyingFinset E)).coeff (2^(d-1)) *
        ((a : K)^(2^(d-1)) * ((a : K)⁻¹)^(2^(d-1)))) := by ac_rfl
    _ = (a : K)^(2^(d-1)) * (rootProduct (underlyingFinset E)).coeff (2^(d-1)) := by
      rw [← mul_pow, mul_inv_cancel₀ ha, one_pow, mul_one]

omit [DecidableEq K] in
theorem nextCoefficient_zero_scalarSubspace_iff (E : Submodule (ZMod 2) K) (a : Kˣ)
    (hd : 0 < Module.finrank (ZMod 2) E) :
    nextFrobeniusCoefficient (scalarSubspace E a) = 0 ↔ nextFrobeniusCoefficient E = 0 := by
  classical
  rw [nextCoefficient_scalarSubspace E a hd, mul_eq_zero]
  simp [pow_ne_zero _ (Units.ne_zero a)]

#print axioms scalarSubspace_subspacePolynomial
#print axioms nextCoefficient_scalarSubspace
#print axioms nextCoefficient_zero_scalarSubspace_iff

end Carlet
