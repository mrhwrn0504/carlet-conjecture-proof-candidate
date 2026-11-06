import Carlet.ArtinSchreierPolynomial
import Carlet.K4ArtinSchreierFactorProbe
import Carlet.K4TraceShiftProbe

noncomputable section
open Polynomial
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

def k4Line : Submodule (ZMod 2) K := Submodule.span (ZMod 2) ({1} : Set K)
def k4Plane (t : K) : Submodule (ZMod 2) K :=
  k4Line ⊔ Submodule.span (ZMod 2) ({t} : Set K)
def k4Space (t : K) : Submodule (ZMod 2) K :=
  k4Plane t ⊔ Submodule.span (ZMod 2) ({t^2} : Set K)
def k4P1 : K[X] := X^2 + X
def k4P2 (t : K) : K[X] := k4P1^2 + C (t^2+t) * k4P1
def k4P3 (t : K) : K[X] :=
  k4P2 t^2 + C ((t^2+t)^3*((t^2+t)+1)) * k4P2 t

theorem k4Plane_polynomial (t : K) (ht : t ∉ k4Line) :
    rootProduct (underlyingFinset (k4Plane t)) = k4P2 t := by
  rw [k4Plane, subspacePolynomial_extension _ t ht]
  change rootProduct (underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K))) ^ 2 +
      C ((rootProduct (underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K)))).eval t) *
        rootProduct (underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K))) = k4P2 t
  rw [primeLine_polynomial]
  simp [k4P2, k4P1]

theorem k4Space_polynomial (t : K) (ht : t ∉ k4Line)
    (ht2 : t^2 ∉ k4Plane t) :
    rootProduct (underlyingFinset (k4Space t)) = k4P3 t := by
  rw [k4Space, subspacePolynomial_extension _ (t^2) ht2, k4Plane_polynomial t ht]
  simp only [k4P2, k4P1, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  rw [k4_extension_parameter]
  rfl

omit [DecidableEq K] in
theorem k4Space_finrank (t : K) (ht : t ∉ k4Line)
    (ht2 : t^2 ∉ k4Plane t) : Module.finrank (ZMod 2) (k4Space t) = 3 := by
  rw [k4Space, extension_finrank _ _ ht2, k4Plane, extension_finrank _ _ ht]
  have h : Module.finrank (ZMod 2) (k4Line : Submodule (ZMod 2) K) = 1 := by
    change Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({(1 : K)} : Set K)) = 1
    exact finrank_span_singleton (K := ZMod 2) (V := K) (one_ne_zero : (1 : K) ≠ 0)
  rw [h]

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem k4P2_coeff_zero (t : K) : (k4P2 t).coeff 0 = 0 := by
  simp [k4P2, k4P1, pow_two, Polynomial.coeff_mul]

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem k4P2_coeff_one (t : K) : (k4P2 t).coeff 1 = t^2+t := by
  simp [k4P2, k4P1, pow_two, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem k4P2_coeff_two (t : K) : (k4P2 t).coeff 2 = 1+(t^2+t) := by
  simp [k4P2, k4P1, pow_two, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ,
    Polynomial.coeff_X]

omit [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K] in
theorem k4P3_coeff_one (t : K) :
    (k4P3 t).coeff 1 = (t^2+t)^4*((t^2+t)+1) := by
  have hs : ((k4P2 t)^2).coeff 1 = 0 := by
    rw [pow_two, Polynomial.mul_coeff_one, k4P2_coeff_zero]
    simp
  change ((k4P2 t)^2).coeff 1 +
    (C ((t^2+t)^3*((t^2+t)+1)) * k4P2 t).coeff 1 = _
  rw [hs, Polynomial.coeff_C_mul, k4P2_coeff_one]
  ring

omit [Fintype K] [DecidableEq K] in
theorem k4P3_coeff_two (t : K) :
    (k4P3 t).coeff 2 = (t^2+t)^2*((t^2+t)^3+(t^2+t)+1) := by
  rw [k4P3, extension_coeff_two _ _ (k4P2_coeff_zero t),
    k4P2_coeff_one, k4P2_coeff_two]
  exact k4_second_coefficient_factor (t^2+t)

/-- Explicit sufficient conditions; finding such parameters uniformly is still open here. -/
theorem hasZeroSumSubspace_four_of_k4_as_chain (t u z s v : K)
    (hu_eq : u = t^2+t) (ht : t ∉ k4Line) (ht2 : t^2 ∉ k4Plane t)
    (hu : u ≠ 0) (hd : u^3+u+1 ≠ 0)
    (hz : z^2+z = 1/(u^3+u+1))
    (hs : s^2+s = u*(u+1)*z) (hv : v^2+v = u*s) :
    HasZeroSumSubspace K 4 := by
  subst u
  have hc2 : (rootProduct (underlyingFinset (k4Space t))).coeff 2 ≠ 0 := by
    rw [k4Space_polynomial t ht ht2, k4P3_coeff_two]
    exact mul_ne_zero (pow_ne_zero _ hu) hd
  have heval : (rootProduct (underlyingFinset (k4Space t))).eval v =
      ((t^2+t)^3*((t^2+t)+1))^2 / ((t^2+t)^3+(t^2+t)+1) := by
    rw [k4Space_polynomial t ht ht2]
    simpa [k4P3, k4P2, k4P1] using
      (k4_artin_schreier_chain (t^2+t) z s v hz hs hv)
  have hratio : (rootProduct (underlyingFinset (k4Space t))).coeff 1 ^ 2 /
      (rootProduct (underlyingFinset (k4Space t))).coeff 2 =
      ((t^2+t)^3*((t^2+t)+1))^2 / ((t^2+t)^3+(t^2+t)+1) := by
    rw [k4Space_polynomial t ht ht2, k4P3_coeff_one, k4P3_coeff_two]
    exact k4_coefficient_ratio_factor (t^2+t) hu
  have himage : (rootProduct (underlyingFinset (k4Space t))).coeff 1 ^ 2 /
      (rootProduct (underlyingFinset (k4Space t))).coeff 2 ∈
        LinearMap.range (subspacePolynomialMap (k4Space t)) := by
    refine ⟨v, ?_⟩
    change (rootProduct (underlyingFinset (k4Space t))).eval v = _
    exact heval.trans hratio.symm
  have h := solver_yields_zeroSum_subspace (k4Space t) hc2 himage
  simpa [k4Space_finrank t ht ht2] using h

/-- The independent-span conditions follow from two explicit nonvanishing tests. -/
theorem hasZeroSumSubspace_four_of_k4_as_parameters (t u z s v : K)
    (hu_eq : u = t^2+t) (hu : u ≠ 0) (hu1 : u+1 ≠ 0) (hd : u^3+u+1 ≠ 0)
    (hz : z^2+z = 1/(u^3+u+1))
    (hs : s^2+s = u*(u+1)*z) (hv : v^2+v = u*s) :
    HasZeroSumSubspace K 4 := by
  have hline : rootProduct (underlyingFinset (k4Line : Submodule (ZMod 2) K)) = k4P1 := by
    change rootProduct (underlyingFinset (Submodule.span (ZMod 2) ({1} : Set K))) = _
    exact primeLine_polynomial
  have ht : t ∉ k4Line := by
    intro hmem
    have hz' := (subspacePolynomial_eval_eq_zero_iff k4Line t).mpr hmem
    rw [hline] at hz'
    have : t^2+t=0 := by simpa [k4P1] using hz'
    exact hu (hu_eq.trans this)
  have hval : (k4P2 t).eval (t^2) = (t^2+t)^3*((t^2+t)+1) := by
    simpa [k4P2, k4P1] using k4_extension_parameter t
  have ht2 : t^2 ∉ k4Plane t := by
    intro hmem
    have hz' := (subspacePolynomial_eval_eq_zero_iff (k4Plane t) (t^2)).mpr hmem
    rw [k4Plane_polynomial t ht, hval, ← hu_eq] at hz'
    exact (mul_ne_zero (pow_ne_zero _ hu) hu1) hz'
  exact hasZeroSumSubspace_four_of_k4_as_chain t u z s v hu_eq ht ht2 hu hd hz hs hv

/-- Two trace tests provide the outer Artin–Schreier roots. -/
theorem hasZeroSumSubspace_four_of_k4_trace_parameters (u z s : K)
    (hu : u ≠ 0) (hu1 : u+1 ≠ 0) (hd : u^3+u+1 ≠ 0)
    (htrace_u : Algebra.trace (ZMod 2) K u = 0)
    (hz : z^2+z = 1/(u^3+u+1))
    (hs : s^2+s = u*(u+1)*z)
    (htrace_us : Algebra.trace (ZMod 2) K (u*s) = 0) :
    HasZeroSumSubspace K 4 := by
  have hu_range : u ∈ LinearMap.range (artinSchreier (K := K)) := by
    rw [artinSchreier_range]
    exact htrace_u
  obtain ⟨t, ht⟩ := hu_range
  have hu_eq : u = t^2+t := by simpa only [artinSchreier_apply] using ht.symm
  have hus_range : u*s ∈ LinearMap.range (artinSchreier (K := K)) := by
    rw [artinSchreier_range]
    exact htrace_us
  obtain ⟨v, hv⟩ := hus_range
  have hv_eq : v^2+v = u*s := by simpa only [artinSchreier_apply] using hv
  exact hasZeroSumSubspace_four_of_k4_as_parameters t u z s v hu_eq hu hu1 hd hz hs hv_eq

/-- In odd degree, the trace-zero condition automatically excludes u = 1. -/
theorem hasZeroSumSubspace_four_of_k4_odd_trace_parameters (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hodd : Odd n) (u z s : K)
    (hu : u ≠ 0) (hd : u^3+u+1 ≠ 0)
    (htrace_u : Algebra.trace (ZMod 2) K u = 0)
    (hz : z^2+z = 1/(u^3+u+1))
    (hs : s^2+s = u*(u+1)*z)
    (htrace_us : Algebra.trace (ZMod 2) K (u*s) = 0) :
    HasZeroSumSubspace K 4 := by
  have htrace_one := Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2)
  simp only [map_one, hn, nsmul_eq_mul, mul_one, hodd.natCast_zmod_two] at htrace_one
  have hu1 : u+1 ≠ 0 := by
    intro h
    have heq : u = 1 := CharTwo.add_eq_zero.mp h
    rw [heq, htrace_one] at htrace_u
    exact one_ne_zero htrace_u
  exact hasZeroSumSubspace_four_of_k4_trace_parameters u z s hu hu1 hd htrace_u hz hs htrace_us

omit [DecidableEq K] in
/-- Eliminate the choice of the middle Artin–Schreier root from the last trace test. -/
theorem k4_trace_eliminate_middle (t u z s : K)
    (hu : u = t^2+t) (hs : s^2+s = u*(u+1)*z) :
    Algebra.trace (ZMod 2) K (u*s) =
      Algebra.trace (ZMod 2) K (t^2*u*(u+1)*z) := by
  have hts : Algebra.trace (ZMod 2) K (t*s) =
      Algebra.trace (ZMod 2) K (t^2*s^2) := by
    simpa only [mul_pow] using (trace_square (t*s)).symm
  calc
    Algebra.trace (ZMod 2) K (u*s) =
        Algebra.trace (ZMod 2) K (t^2*s + t*s) := by rw [hu]; congr 1; ring
    _ = Algebra.trace (ZMod 2) K (t^2*s) + Algebra.trace (ZMod 2) K (t*s) := by rw [map_add]
    _ = Algebra.trace (ZMod 2) K (t^2*s) + Algebra.trace (ZMod 2) K (t^2*s^2) := by rw [hts]
    _ = Algebra.trace (ZMod 2) K (t^2*(s+s^2)) := by rw [mul_add, map_add]
    _ = Algebra.trace (ZMod 2) K (t^2*u*(u+1)*z) := by
      congr 1
      rw [add_comm s (s^2), hs]
      ring

/-- A two-parameter sufficient criterion; the existence of such parameters remains to be proved. -/
theorem hasZeroSumSubspace_four_of_k4_two_parameters (t z : K)
    (hu : t^2+t ≠ 0) (hu1 : t^2+t+1 ≠ 0)
    (hd : (t^2+t)^3+(t^2+t)+1 ≠ 0)
    (hz : z^2+z = 1/((t^2+t)^3+(t^2+t)+1))
    (htrace1 : Algebra.trace (ZMod 2) K ((t^2+t)*((t^2+t)+1)*z) = 0)
    (htrace2 : Algebra.trace (ZMod 2) K (t^2*(t^2+t)*((t^2+t)+1)*z) = 0) :
    HasZeroSumSubspace K 4 := by
  let u := t^2+t
  have htrace_u : Algebra.trace (ZMod 2) K u = 0 := by
    dsimp [u]
    rw [map_add, trace_square, CharTwo.add_self_eq_zero]
  have hs_range : u*(u+1)*z ∈ LinearMap.range (artinSchreier (K := K)) := by
    rw [artinSchreier_range]
    exact htrace1
  obtain ⟨s, hs⟩ := hs_range
  have hs_eq : s^2+s = u*(u+1)*z := by simpa only [artinSchreier_apply] using hs
  have htrace_us : Algebra.trace (ZMod 2) K (u*s) = 0 := by
    rw [k4_trace_eliminate_middle t u z s rfl hs_eq]
    exact htrace2
  exact hasZeroSumSubspace_four_of_k4_trace_parameters u z s hu hu1 hd htrace_u hz hs_eq htrace_us

/-- A single parameter satisfying three explicit rational trace tests is sufficient. -/
theorem hasZeroSumSubspace_four_of_k4_rational_traces (t : K)
    (hu : t^2+t ≠ 0) (hu1 : t^2+t+1 ≠ 0)
    (hd : (t^2+t)^3+(t^2+t)+1 ≠ 0)
    (htrace0 : Algebra.trace (ZMod 2) K (1/((t^2+t)^3+(t^2+t)+1)) = 0)
    (htrace1 : Algebra.trace (ZMod 2) K ((t^2+t)^2/((t^2+t)^3+(t^2+t)+1)) = 0)
    (htrace2 : Algebra.trace (ZMod 2) K (t^6/((t^2+t)^3+(t^2+t)+1)) = 0) :
    HasZeroSumSubspace K 4 := by
  have hz_range : 1/((t^2+t)^3+(t^2+t)+1) ∈ LinearMap.range (artinSchreier (K := K)) := by
    rw [artinSchreier_range]
    exact htrace0
  obtain ⟨z, hz⟩ := hz_range
  have hz_eq : z^2+z = 1/((t^2+t)^3+(t^2+t)+1) := by
    simpa only [artinSchreier_apply] using hz
  have ht1 : Algebra.trace (ZMod 2) K ((t^2+t)*((t^2+t)+1)*z) = 0 := by
    have heq : (t^2+t)*((t^2+t)+1)*z = ((t^2+t)^2+(t^2+t))*z := by ring
    rw [heq, k4_trace_as_pair, hz_eq]
    simpa [div_eq_mul_inv] using htrace1
  have ht2 : Algebra.trace (ZMod 2) K (t^2*(t^2+t)*((t^2+t)+1)*z) = 0 := by
    have heq : t^2*(t^2+t)*((t^2+t)+1)*z = ((t^3)^2+t^3)*z := by
      rw [k4_second_trace_polynomial]
    rw [heq, k4_trace_as_pair, hz_eq]
    have hsquare : (t^3)^2 = t^6 := by ring
    rw [hsquare]
    simpa [div_eq_mul_inv] using htrace2
  exact hasZeroSumSubspace_four_of_k4_two_parameters t z hu hu1 hd hz_eq ht1 ht2

#print axioms k4Plane_polynomial
#print axioms k4Space_polynomial
#print axioms k4Space_finrank
#print axioms k4P3_coeff_one
#print axioms k4P3_coeff_two
#print axioms hasZeroSumSubspace_four_of_k4_as_chain
#print axioms hasZeroSumSubspace_four_of_k4_as_parameters
#print axioms hasZeroSumSubspace_four_of_k4_trace_parameters
#print axioms hasZeroSumSubspace_four_of_k4_odd_trace_parameters
#print axioms k4_trace_eliminate_middle
#print axioms hasZeroSumSubspace_four_of_k4_two_parameters
#print axioms hasZeroSumSubspace_four_of_k4_rational_traces
end Carlet
