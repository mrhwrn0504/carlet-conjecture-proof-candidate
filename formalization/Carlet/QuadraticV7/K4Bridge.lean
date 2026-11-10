import Carlet.QuadraticV7.Elimination
import Carlet.K4ParametricExtensionProbe
import Mathlib.Tactic

noncomputable section

namespace Carlet.QuadraticV7

variable {K : Type} [Field K]

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

section TriangularRelations

variable [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

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
          (t ^ 2) ^ 2 + t ^ 2 = (t ^ 2 + t) ^ 2 := hpow.symm
          _ = (t ^ 2 + t) * (t ^ 2 + t) := by rw [pow_two]
      · simp [k4V7Entry, k4V7Coefficients]
        ring
    · have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl
      · simpa [k4V7Entry, k4V7Coefficients] using hv
      · simpa [k4V7Entry, k4V7Coefficients] using hs
      · simpa [k4V7Entry, k4V7Coefficients] using hz

end TriangularRelations

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

section K4Construction

variable [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

/-- Thus the concrete v7 triangular system is already sufficient for the
    established K4 subspace construction (under its explicit nonvanishing
    hypotheses). -/
theorem hasZeroSumSubspace_four_of_k4V7_triangular
    [Fintype K] [DecidableEq K] (t q z s v : K)
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


section TraceForward

variable [Fintype K] [DecidableEq K]

/-- The three rational trace tests used by the K4 construction produce a
    concrete solution of the v7 eliminated system.  This identifies the
    remaining existence problem with finding one parameter t satisfying
    those three trace conditions. -/
omit [DecidableEq K] in
theorem k4V7_eliminatedSystem_of_rational_traces
    (t : K)
    (hq0 : t ^ 2 + t ≠ 0)
    (hq1 : t ^ 2 + t + 1 ≠ 0)
    (hD : (t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1 ≠ 0)
    (htrace0 : Algebra.trace (ZMod 2) K
      (1 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0)
    (htrace1 : Algebra.trace (ZMod 2) K
      ((t ^ 2 + t) ^ 2 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0)
    (htrace2 : Algebra.trace (ZMod 2) K
      (t ^ 6 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0) :
    ∃ z s v : K,
      EliminatedSystem 4 (by omega) (k4V7Entry t (t ^ 2 + t) z s v)
        (truncate 4 (k4V7T (t ^ 2 + t)))
        (k4V7Coefficients (t ^ 2 + t)) := by
  let q : K := t ^ 2 + t
  have hq : q = t ^ 2 + t := rfl
  have hq0' : q ≠ 0 := by simpa [q] using hq0
  have hq1' : q + 1 ≠ 0 := by simpa [q] using hq1
  have hD' : q ^ 3 + q + 1 ≠ 0 := by simpa [q] using hD
  have htrace0' : Algebra.trace (ZMod 2) K
      (1 / (q ^ 3 + q + 1)) = 0 := by
    simpa [q] using htrace0
  have htrace1' : Algebra.trace (ZMod 2) K
      (q ^ 2 / (q ^ 3 + q + 1)) = 0 := by
    simpa [q] using htrace1
  have htrace2' : Algebra.trace (ZMod 2) K
      (t ^ 6 / (q ^ 3 + q + 1)) = 0 := by
    simpa [q] using htrace2
  have hz_range : 1 / (q ^ 3 + q + 1) ∈
      LinearMap.range (Carlet.artinSchreier (K := K)) := by
    rw [Carlet.artinSchreier_range]
    exact htrace0'
  obtain ⟨z, hz⟩ := hz_range
  have hz_eq : z ^ 2 + z = (q ^ 3 + q + 1)⁻¹ := by
    simpa [Carlet.artinSchreier_apply, div_eq_mul_inv] using hz
  have htrace_qz : Algebra.trace (ZMod 2) K (q * (q + 1) * z) = 0 := by
    have hfactor : q * (q + 1) * z = (q ^ 2 + q) * z := by ring
    rw [hfactor, Carlet.k4_trace_as_pair, hz_eq]
    simpa [div_eq_mul_inv] using htrace1'
  have hs_range : q * (q + 1) * z ∈
      LinearMap.range (Carlet.artinSchreier (K := K)) := by
    rw [Carlet.artinSchreier_range]
    exact htrace_qz
  obtain ⟨s, hs⟩ := hs_range
  have hs_eq : s ^ 2 + s = q * (q + 1) * z := by
    simpa only [Carlet.artinSchreier_apply] using hs
  have htrace_qs : Algebra.trace (ZMod 2) K (q * s) = 0 := by
    rw [Carlet.k4_trace_eliminate_middle t q z s hq hs_eq]
    have hpoly : t ^ 2 * q * (q + 1) * z =
        ((t ^ 3) ^ 2 + t ^ 3) * z := by
      calc
        t ^ 2 * q * (q + 1) * z =
            (t ^ 2 * (t ^ 2 + t) * ((t ^ 2 + t) + 1)) * z := by
              rw [hq]
        _ = ((t ^ 3) ^ 2 + t ^ 3) * z := by
              rw [k4_second_trace_polynomial]
    rw [hpoly, Carlet.k4_trace_as_pair, hz_eq]
    have hsquare : (t ^ 3) ^ 2 = t ^ 6 := by ring
    rw [hsquare]
    simpa [div_eq_mul_inv] using htrace2'
  have hv_range : q * s ∈
      LinearMap.range (Carlet.artinSchreier (K := K)) := by
    rw [Carlet.artinSchreier_range]
    exact htrace_qs
  obtain ⟨v, hv⟩ := hv_range
  have hv_eq : v ^ 2 + v = q * s := by
    simpa only [Carlet.artinSchreier_apply] using hv
  exact ⟨z, s, v,
    k4V7_eliminatedSystem_of_chain t q z s v
      hq hq0' hq1' hD' hz_eq hs_eq hv_eq⟩


end TraceForward

section TraceBackward

variable [Fintype K]

/-- Conversely, every v7 eliminated solution forces all three rational
    trace conditions.  Thus the trace tests are not merely sufficient:
    they exactly encode the existence of this concrete K4 chain. -/
theorem k4V7_rational_traces_of_eliminatedSystem
    (t q z s v : K)
    (hsys : EliminatedSystem 4 (by omega) (k4V7Entry t q z s v)
      (truncate 4 (k4V7T q)) (k4V7Coefficients q)) :
    Algebra.trace (ZMod 2) K (1 / (q ^ 3 + q + 1)) = 0 ∧
      Algebra.trace (ZMod 2) K (q ^ 2 / (q ^ 3 + q + 1)) = 0 ∧
      Algebra.trace (ZMod 2) K (t ^ 6 / (q ^ 3 + q + 1)) = 0 := by
  obtain ⟨hq, hz, hs, hv⟩ :=
    k4_parameters_of_v7_triangular t q z s v hsys.1
  have htrace0 : Algebra.trace (ZMod 2) K
      ((q ^ 3 + q + 1)⁻¹) = 0 := by
    rw [← hz, map_add, Carlet.trace_square, CharTwo.add_self_eq_zero]
  have htrace_qz : Algebra.trace (ZMod 2) K (q * (q + 1) * z) = 0 := by
    rw [← hs, map_add, Carlet.trace_square, CharTwo.add_self_eq_zero]
  have hfactor : q * (q + 1) * z = (q ^ 2 + q) * z := by ring
  have htrace1 : Algebra.trace (ZMod 2) K
      (q ^ 2 * (q ^ 3 + q + 1)⁻¹) = 0 := by
    calc
      _ = Algebra.trace (ZMod 2) K (q ^ 2 * (z ^ 2 + z)) := by rw [hz]
      _ = Algebra.trace (ZMod 2) K ((q ^ 2 + q) * z) :=
        (Carlet.k4_trace_as_pair q z).symm
      _ = Algebra.trace (ZMod 2) K (q * (q + 1) * z) := by rw [hfactor]
      _ = 0 := htrace_qz
  have htrace_qs : Algebra.trace (ZMod 2) K (q * s) = 0 := by
    rw [← hv, map_add, Carlet.trace_square, CharTwo.add_self_eq_zero]
  have hpoly : t ^ 2 * q * (q + 1) = (t ^ 3) ^ 2 + t ^ 3 := by
    calc
      t ^ 2 * q * (q + 1) =
          t ^ 2 * (t ^ 2 + t) * ((t ^ 2 + t) + 1) := by rw [hq]
      _ = (t ^ 3) ^ 2 + t ^ 3 := k4_second_trace_polynomial t
  have hsquare : (t ^ 3) ^ 2 = t ^ 6 := by ring
  have htrace2 : Algebra.trace (ZMod 2) K
      (t ^ 6 * (q ^ 3 + q + 1)⁻¹) = 0 := by
    calc
      _ = Algebra.trace (ZMod 2) K ((t ^ 3) ^ 2 * (z ^ 2 + z)) := by
        rw [← hsquare, hz]
      _ = Algebra.trace (ZMod 2) K (((t ^ 3) ^ 2 + t ^ 3) * z) :=
        (Carlet.k4_trace_as_pair (t ^ 3) z).symm
      _ = Algebra.trace (ZMod 2) K (t ^ 2 * q * (q + 1) * z) := by
        rw [← hpoly]
      _ = Algebra.trace (ZMod 2) K (q * s) :=
        (Carlet.k4_trace_eliminate_middle t q z s hq hs).symm
      _ = 0 := htrace_qs
  exact ⟨by simpa [div_eq_mul_inv] using htrace0,
    by simpa [div_eq_mul_inv] using htrace1,
    by simpa [div_eq_mul_inv] using htrace2⟩

end TraceBackward

section TraceConclusion

variable [Fintype K] [DecidableEq K]

/-- Exact equivalence between the v7 eliminated K4 system and the three
    one-parameter rational trace conditions, under the required
    nonvanishing conditions. -/
theorem k4V7_rational_trace_criterion_iff
    (t : K)
    (hq0 : t ^ 2 + t ≠ 0)
    (hq1 : t ^ 2 + t + 1 ≠ 0)
    (hD : (t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1 ≠ 0) :
    (∃ z s v : K,
      EliminatedSystem 4 (by omega)
        (k4V7Entry t (t ^ 2 + t) z s v)
        (truncate 4 (k4V7T (t ^ 2 + t)))
        (k4V7Coefficients (t ^ 2 + t))) ↔
      Algebra.trace (ZMod 2) K
        (1 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0 ∧
      Algebra.trace (ZMod 2) K
        ((t ^ 2 + t) ^ 2 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0 ∧
      Algebra.trace (ZMod 2) K
        (t ^ 6 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0 := by
  constructor
  · rintro ⟨z, s, v, hsys⟩
    exact k4V7_rational_traces_of_eliminatedSystem
      t (t ^ 2 + t) z s v hsys
  · rintro ⟨htrace0, htrace1, htrace2⟩
    obtain ⟨z, s, v, hsys⟩ :=
      k4V7_eliminatedSystem_of_rational_traces
        t hq0 hq1 hD htrace0 htrace1 htrace2
    exact ⟨z, s, v, hsys⟩


/-- A rational-trace witness therefore yields the desired four-dimensional
    zero-sum subspace through the v7 eliminated system. -/
theorem hasZeroSumSubspace_four_of_k4V7_traceWitness
    (t : K)
    (hq0 : t ^ 2 + t ≠ 0)
    (hq1 : t ^ 2 + t + 1 ≠ 0)
    (hD : (t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1 ≠ 0)
    (htrace0 : Algebra.trace (ZMod 2) K
      (1 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0)
    (htrace1 : Algebra.trace (ZMod 2) K
      ((t ^ 2 + t) ^ 2 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0)
    (htrace2 : Algebra.trace (ZMod 2) K
      (t ^ 6 / ((t ^ 2 + t) ^ 3 + (t ^ 2 + t) + 1)) = 0) :
    Carlet.HasZeroSumSubspace K 4 := by
  obtain ⟨z, s, v, hsys⟩ :=
    k4V7_eliminatedSystem_of_rational_traces
      t hq0 hq1 hD htrace0 htrace1 htrace2
  exact hasZeroSumSubspace_four_of_k4V7_triangular
    t (t ^ 2 + t) z s v hq0 hq1 hD hsys.1

end TraceConclusion

#print axioms k4V7_triangularRelations
#print axioms k4_parameters_of_v7_triangular
#print axioms hasZeroSumSubspace_four_of_k4V7_triangular
#print axioms k4V7_originalSystem_of_chain
#print axioms k4V7_eliminatedSystem_of_chain
#print axioms k4V7_eliminatedSystem_of_rational_traces
#print axioms k4V7_rational_traces_of_eliminatedSystem
#print axioms k4V7_rational_trace_criterion_iff
#print axioms hasZeroSumSubspace_four_of_k4V7_traceWitness

end K4Construction

end Carlet.QuadraticV7