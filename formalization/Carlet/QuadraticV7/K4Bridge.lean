import Carlet.QuadraticV7.Elimination
import Carlet.K4ParametricExtensionProbe
import Mathlib.Tactic

noncomputable section

namespace Carlet.QuadraticV7

variable {K : Type} [Field K] [Fintype K]
  [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- The three scale factors in the four-level K4 Artin--Schreier chain. -/
def k4V7Coefficients (q : K) (j : ℕ) : K :=
  if j = 1 then q
  else if j = 2 then q * (q + 1)
  else if j = 3 then (q ^ 3 + q + 1)⁻¹
  else 0

/-- The lower-triangular array of Artin--Schreier roots used by the K4
    parameter construction, embedded into the v7 triangular system. -/
def k4V7Entry (t q z s v : K) (a j : ℕ) : K :=
  if a = 2 then (if j = 1 then t else 1)
  else if a = 3 then (if j = 1 then t ^ 2 else if j = 2 then q else 1)
  else if a = 4 then
    (if j = 1 then v else if j = 2 then s else if j = 3 then z else 1)
  else 0

/-- The reciprocal chain t₀,…,t₃ determined by the K4 scale factors. -/
def k4V7T (q : K) : Fin 4 → K :=
  fun i =>
    if i.val = 0 then 1
    else if i.val = 1 then q⁻¹
    else if i.val = 2 then (q ^ 2 * (q + 1))⁻¹
    else (q ^ 3 + q + 1) * (q ^ 2 * (q + 1))⁻¹

/-- The actual K4 Artin--Schreier chain satisfies every triangular
    relation required by v7. -/
theorem k4V7_triangularRelations (t q z s v : K)
    (hq : q = t ^ 2 + t)
    (hz : z ^ 2 + z = (q ^ 3 + q + 1)⁻¹)
    (hs : s ^ 2 + s = q * (q + 1) * z)
    (hv : v ^ 2 + v = q * s) :
    TriangularRelations (k4V7Entry t q z s v)
      (k4V7Coefficients q) 4 := by
  constructor
  · intro a ha₁ ha₂
    have ha : a = 2 ∨ a = 3 ∨ a = 4 := by omega
    rcases ha with rfl | rfl | rfl <;> simp [k4V7Entry]
  · intro a ha₁ ha₂ j hj₁ hja
    have ha : a = 2 ∨ a = 3 ∨ a = 4 := by omega
    rcases ha with rfl | rfl | rfl
    · have hj : j = 1 := by omega
      subst j
      simp [k4V7Entry, k4V7Coefficients, hq]
    · have hj : j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl
      · simp [k4V7Entry, k4V7Coefficients]
        rw [hq]
        have hpow : (t ^ 2 + t) ^ 2 = (t ^ 2) ^ 2 + t ^ 2 := by
          simpa using (add_pow_char (t ^ 2) t 2)
        calc
          t ^ 2 + (t ^ 2) ^ 2 = (t ^ 2) ^ 2 + t ^ 2 := by ac_rfl
          _ = (t ^ 2 + t) ^ 2 := hpow.symm
          _ = (t ^ 2 + t) * (t ^ 2 + t) := by rw [pow_two]
      · simp [k4V7Entry, k4V7Coefficients]
        ring
    · have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl
      · simpa [k4V7Entry, k4V7Coefficients] using hv
      · simpa [k4V7Entry, k4V7Coefficients] using hs
      · simpa [k4V7Entry, k4V7Coefficients] using hz

/-- The v7 triangular relations for this concrete array recover precisely
    the K4 parameter equations. -/
theorem k4_parameters_of_v7_triangular (t q z s v : K)
    (htri : TriangularRelations (k4V7Entry t q z s v)
      (k4V7Coefficients q) 4) :
    q = t ^ 2 + t ∧
      z ^ 2 + z = (q ^ 3 + q + 1)⁻¹ ∧
      s ^ 2 + s = q * (q + 1) * z ∧
      v ^ 2 + v = q * s := by
  have hq : q = t ^ 2 + t := by
    have h := htri.2 2 (by omega) (by omega) 1 (by omega) (by omega)
    simpa [k4V7Entry, k4V7Coefficients] using h.symm
  have hz : z ^ 2 + z = (q ^ 3 + q + 1)⁻¹ := by
    have h := htri.2 4 (by omega) (by omega) 3 (by omega) (by omega)
    simpa [k4V7Entry, k4V7Coefficients] using h
  have hs : s ^ 2 + s = q * (q + 1) * z := by
    have h := htri.2 4 (by omega) (by omega) 2 (by omega) (by omega)
    simpa [k4V7Entry, k4V7Coefficients] using h
  have hv : v ^ 2 + v = q * s := by
    have h := htri.2 4 (by omega) (by omega) 1 (by omega) (by omega)
    simpa [k4V7Entry, k4V7Coefficients] using h
  exact ⟨hq, hz, hs, hv⟩

/-- Thus the concrete v7 triangular system is already sufficient for the
    established K4 subspace construction (under its explicit nonvanishing
    hypotheses). -/
theorem hasZeroSumSubspace_four_of_k4V7_triangular
    (t q z s v : K)
    (hq0 : q ≠ 0) (hq1 : q + 1 ≠ 0)
    (hD : q ^ 3 + q + 1 ≠ 0)
    (htri : TriangularRelations (k4V7Entry t q z s v)
      (k4V7Coefficients q) 4) :
    Carlet.HasZeroSumSubspace K 4 := by
  obtain ⟨hq, hz, hs, hv⟩ :=
    k4_parameters_of_v7_triangular t q z s v htri
  have hz' : z ^ 2 + z = 1 / (q ^ 3 + q + 1) := by
    simpa [div_eq_mul_inv] using hz
  exact Carlet.hasZeroSumSubspace_four_of_k4_as_parameters
    t q z s v hq hq0 hq1 hD hz' hs hv

/-- The concrete K4 chain supplies a full solution of the v7 original
    system, including the reciprocal recurrence and the terminal sum. -/
theorem k4V7_originalSystem_of_chain
    (t q z s v : K)
    (hq : q = t ^ 2 + t)
    (hq0 : q ≠ 0) (hq1 : q + 1 ≠ 0)
    (hD : q ^ 3 + q + 1 ≠ 0)
    (hz : z ^ 2 + z = (q ^ 3 + q + 1)⁻¹)
    (hs : s ^ 2 + s = q * (q + 1) * z)
    (hv : v ^ 2 + v = q * s) :
    OriginalSystem 4 (by omega) (k4V7Entry t q z s v)
      (k4V7T q) (k4V7Coefficients q) := by
  have htri := k4V7_triangularRelations t q z s v hq hz hs hv
  have hden : q ^ 2 * (q + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hq0) hq1
  refine ⟨htri, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · change q * q⁻¹ = 1
      exact mul_inv_cancel₀ hq0
    · change q * (q + 1) * (q ^ 2 * (q + 1))⁻¹ = q⁻¹
      field_simp [hq0, hq1, hden]
    · change (q ^ 3 + q + 1)⁻¹ *
        ((q ^ 3 + q + 1) * (q ^ 2 * (q + 1))⁻¹) =
          (q ^ 2 * (q + 1))⁻¹
      calc
        _ = ((q ^ 3 + q + 1)⁻¹ * (q ^ 3 + q + 1)) *
            (q ^ 2 * (q + 1))⁻¹ := by ring
        _ = 1 * (q ^ 2 * (q + 1))⁻¹ := by
          rw [inv_mul_cancel₀ hD]
        _ = (q ^ 2 * (q + 1))⁻¹ := by simp
  · simp [k4V7T]
  · have htotal :
      totalSum 4 (k4V7T q) =
        q⁻¹ + (q ^ 2 * (q + 1))⁻¹ +
          (q ^ 3 + q + 1) * (q ^ 2 * (q + 1))⁻¹ := by
      simp [totalSum, evalFin, k4V7T, Finset.sum_range_succ]
    have hsum : 1 + totalSum 4 (k4V7T q) = 0 := by
      rw [htotal]
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      field_simp [hq0, hden]
      ring_nf
      simp [htwo]
    exact hsum

/-- Applying the general v7 elimination theorem to the concrete K4 chain
    removes its final reciprocal coordinate without changing solvability. -/
theorem k4V7_eliminatedSystem_of_chain
    (t q z s v : K)
    (hq : q = t ^ 2 + t)
    (hq0 : q ≠ 0) (hq1 : q + 1 ≠ 0)
    (hD : q ^ 3 + q + 1 ≠ 0)
    (hz : z ^ 2 + z = (q ^ 3 + q + 1)⁻¹)
    (hs : s ^ 2 + s = q * (q + 1) * z)
    (hv : v ^ 2 + v = q * s) :
    EliminatedSystem 4 (by omega) (k4V7Entry t q z s v)
      (truncate 4 (k4V7T q)) (k4V7Coefficients q) := by
  have hsys := k4V7_originalSystem_of_chain
    t q z s v hq hq0 hq1 hD hz hs hv
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  exact original_implies_eliminated 4 (by omega)
    (k4V7Entry t q z s v) (k4V7T q) (k4V7Coefficients q) htwo hsys

#print axioms k4V7_triangularRelations
#print axioms k4_parameters_of_v7_triangular
#print axioms hasZeroSumSubspace_four_of_k4V7_triangular
#print axioms k4V7_originalSystem_of_chain
#print axioms k4V7_eliminatedSystem_of_chain

end Carlet.QuadraticV7