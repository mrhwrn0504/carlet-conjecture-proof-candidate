import Carlet.PresentationSchemeIso
import Carlet.CandidatePaper.Section3

set_option linter.style.haveILetI false

/-!
Paper-specific interface for the algebraic-model portion of Section 4 in the
supplied candidate manuscript.  The affine coordinate schemes and their
functor-of-points equivalence are formalized.  Identification of the
`OpenCarletPoint` scheme with the full-rank stratum inside Pink--Schieder's
reciprocal projective compactification is a separate geometric obligation and
is deliberately not asserted here.
-/

noncomputable section

namespace Carlet.CandidatePaper.Section4

open AlgebraicGeometry

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- The manuscript's two affine coordinate presentations have isomorphic
`A`-valued points for every F₂-algebra A. -/
def affine_model_points_equiv (r : ℕ) (hr : 2 ≤ r) :
    Carlet.Quadratic.OpenCarletPoint A r ≃ Carlet.Quadratic.QuadraticPoint A r :=
  Carlet.Quadratic.finiteCoordinateEquiv r (by omega)

/-- The span of the first n coordinates, which is the finite-field version of
the manuscript's E_n in the one-based indexing convention. -/
def prefixSpan {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (n : ℕ) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) (Set.range (fun i : Fin n => x i.val))

/-- Full rank implies linear independence of every coordinate prefix. -/
theorem prefix_coordinates_linearIndependent
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (n : ℕ) (hfull : Carlet.Quadratic.FullRank x (n+1)) :
    LinearIndependent (ZMod 2) (fun i : Fin n => x i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨b, hb⟩ := (Carlet.CandidatePaper.Section3.bitsCoeff_bijective n).2 g
  have hcomb : Carlet.Quadratic.combination x n b = 0 := by
    rw [Carlet.CandidatePaper.Section3.combination_eq_coeff_sum]
    calc
      (∑ j : Fin n, Carlet.CandidatePaper.Section3.bitsCoeff n b j • x j.val) =
          ∑ j : Fin n, g j • x j.val := by rw [hb]
      _ = 0 := hg
  have hbit : b = Carlet.Quadratic.zeroBits n := by
    by_contra hne
    have hpre := Carlet.Quadratic.fullRank_prefix x (n+1) n (by omega) hfull
    have hu := hpre b hne
    exact (isUnit_iff_ne_zero.mp hu) hcomb
  have hcoeff : Carlet.CandidatePaper.Section3.bitsCoeff n b = 0 := by
    rw [hbit, Carlet.CandidatePaper.Section3.bitsCoeff_zeroBits]
  have hg0 : g = 0 := hb.symm.trans hcoeff
  exact congrFun hg0 i

/-- A linearly independent coordinate prefix identifies coefficient vectors
with all elements of its span. -/
noncomputable def prefixCoefficientsEquiv
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (n : ℕ)
    (hli : LinearIndependent (ZMod 2) (fun i : Fin n => x i.val)) :
    (Fin n → ZMod 2) ≃ prefixSpan x n := by
  classical
  let f := Carlet.CandidatePaper.Section3.coefficientCombinationMap n
    (fun i : Fin n => x i.val)
  have hrange : f.range = prefixSpan x n := by
    simpa [f, prefixSpan] using
      (Carlet.CandidatePaper.Section3.coefficientCombinationMap_range n
        (fun i : Fin n => x i.val))
  have hinj : Function.Injective f := by
    rw [Fintype.linearIndependent_iff] at hli
    intro a b hab
    funext i
    have hzero : f (a - b) = 0 := by
      rw [map_sub, hab]
      simp
    have hi := hli (a - b) (by simpa [f, Carlet.CandidatePaper.Section3.coefficientCombinationMap] using hzero) i
    exact sub_eq_zero.mp hi
  apply Equiv.ofBijective
    (fun g => ⟨f g, by rw [← hrange]; exact ⟨g, rfl⟩⟩)
  constructor
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · intro z
    have hz : (z : K) ∈ f.range := by rw [hrange]; exact z.property
    rcases hz with ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

@[simp] theorem prefixCoefficientsEquiv_apply
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (n : ℕ)
    (hli : LinearIndependent (ZMod 2) (fun i : Fin n => x i.val))
    (g : Fin n → ZMod 2) :
    (prefixCoefficientsEquiv x n hli g : K) =
      ∑ i : Fin n, g i • x i.val := by
  simp [prefixCoefficientsEquiv,
    Carlet.CandidatePaper.Section3.coefficientCombinationMap]

/-- The manuscript's fiber reciprocal sum over E_n is the block sum used by
the quadratic reconstruction. The full-rank hypothesis makes the coefficient
indexing bijective with the actual subspace. -/
theorem blockSum_eq_prefixSpan_sum
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (n : ℕ)
    (hfull : Carlet.Quadratic.FullRank x (n+1))
    [Fintype (prefixSpan x n)] :
    Carlet.Quadratic.blockSum x n =
      ∑ e : prefixSpan x n, Ring.inverse (x n + (e : K)) := by
  classical
  let hli := prefix_coordinates_linearIndependent x n hfull
  let e := prefixCoefficientsEquiv x n hli
  calc
    Carlet.Quadratic.blockSum x n =
        ∑ g : Fin n → ZMod 2,
          Ring.inverse (x n + ∑ i : Fin n, g i • x i.val) := by
      unfold Carlet.Quadratic.blockSum
      rw [← Equiv.sum_comp (Carlet.CandidatePaper.Section3.bitsCoeffEquiv n)]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Carlet.CandidatePaper.Section3.bitsCoeffEquiv,
        Equiv.ofBijective_apply]
      rw [Carlet.CandidatePaper.Section3.combination_eq_coeff_sum]
    _ = ∑ e' : prefixSpan x n, Ring.inverse (x n + (e' : K)) := by
      rw [← Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro g hg
      rw [prefixCoefficientsEquiv_apply]

/-- With Lean's zero-based indices, the reciprocal sum f_{n+1} from the
manuscript is exactly t_n = C_n/delta_n in the quadratic coordinates. -/
theorem manuscript_reciprocal_fiber_eq_quadraticT
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (r : ℕ) (n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (hfull : Carlet.Quadratic.FullRank x r)
    [Fintype (prefixSpan x n)] :
    Carlet.Quadratic.forwardT x n =
      ∑ e : prefixSpan x n, Ring.inverse (x n + (e : K)) := by
  have hpre : Carlet.Quadratic.FullRank x (n+1) :=
    Carlet.Quadratic.fullRank_prefix x r (n+1) (by omega) hfull
  rw [Carlet.Quadratic.forwardT_eq_blockSum
    Carlet.Quadratic.algebra_two_eq_zero x r n hn hx hfull]
  exact blockSum_eq_prefixSpan_sum x n hpre

/-- The previous identity is exactly the paper's f_{n+1}=C_n/delta_n
formula: linearScale is the coefficient C_n of X in the subspace polynomial,
and scale is delta_n. -/
theorem manuscript_fiber_sum_eq_linearCoefficient_over_delta
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (r : ℕ) (n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (hfull : Carlet.Quadratic.FullRank x r)
    [Fintype (prefixSpan x n)] :
    (∑ e : prefixSpan x n, Ring.inverse (x n + (e : K))) =
      Carlet.Quadratic.linearScale (Carlet.Quadratic.forwardC x) n *
        Ring.inverse (Carlet.Quadratic.delta x n) := by
  rw [← manuscript_reciprocal_fiber_eq_quadraticT x r n hn hx hfull]
  rw [Carlet.Quadratic.forwardT, Carlet.Quadratic.reciprocalRatio]
  rw [Carlet.Quadratic.forward_scale_eq_delta
    Carlet.Quadratic.algebra_two_eq_zero x r hx hfull n hn]

/-- In the exact paper notation, C_n is the X coefficient of L_n. This
version states Equation (4.2) using the polynomial coefficient directly. -/
theorem manuscript_fiber_sum_eq_subspacePolynomial_coefficient_over_delta
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (x : ℕ → K) (r : ℕ) (n : ℕ) (hn : n < r)
    (hx : x 0 = 1) (hfull : Carlet.Quadratic.FullRank x r)
    [Fintype (prefixSpan x n)] :
    (∑ e : prefixSpan x n, Ring.inverse (x n + (e : K))) =
      (Carlet.Quadratic.kernelPolynomial x n).coeff 1 *
        Ring.inverse (Carlet.Quadratic.delta x n) := by
  have hcoef :
      (Carlet.Quadratic.reconstructedPolynomial
        (Carlet.Quadratic.forwardC x) n).coeff 1 =
        Carlet.Quadratic.linearScale (Carlet.Quadratic.forwardC x) n := by
    have h := congrArg (fun p : Polynomial K => p.coeff 0)
      (Carlet.Quadratic.derivative_reconstructed
        Carlet.Quadratic.algebra_two_eq_zero (Carlet.Quadratic.forwardC x) n)
    rw [Polynomial.coeff_derivative] at h
    simpa using h
  have hrec := Carlet.Quadratic.forward_reconstructed_eq_kernel
    Carlet.Quadratic.algebra_two_eq_zero x r hx hfull n (by omega)
  have hkernelCoeff :
      (Carlet.Quadratic.kernelPolynomial x n).coeff 1 =
        Carlet.Quadratic.linearScale (Carlet.Quadratic.forwardC x) n := by
    rw [← hrec]
    exact hcoef
  calc
    _ = Carlet.Quadratic.linearScale (Carlet.Quadratic.forwardC x) n *
          Ring.inverse (Carlet.Quadratic.delta x n) :=
        manuscript_fiber_sum_eq_linearCoefficient_over_delta
          x r n hn hx hfull
    _ = _ := by rw [hkernelCoeff.symm]

/-- The finite-field points of the manuscript's quadratic affine model exist
exactly when the corresponding zero-sum subspace exists. This wires the
Section 3 subspace correspondence into the Section 4 complete-intersection
coordinates, without asserting an identification with the projective
compactification. -/
theorem exists_quadraticPoint_iff_hasZeroSumSubspace
    {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (r : ℕ) (hr : 2 ≤ r) :
    Nonempty (Carlet.Quadratic.QuadraticPoint K r) ↔
      Carlet.HasZeroSumSubspace K r := by
  let e := affine_model_points_equiv (A := K) r hr
  have hrpos : 0 < r := by omega
  constructor
  · rintro ⟨q⟩
    exact (Carlet.CandidatePaper.Section3.exists_openPoint_iff_hasZeroSumSubspace
      r hrpos).mp ⟨e.symm q⟩
  · intro h
    rcases (Carlet.CandidatePaper.Section3.exists_openPoint_iff_hasZeroSumSubspace
      r hrpos).mpr h with ⟨p⟩
    exact ⟨e p⟩

/-- The represented open-equation and quadratic-equation affine schemes are
isomorphic. This is the formalized affine presentation result, conditional on
neither finite-field points nor reducedness. It is not by itself the Pink–
Schieder reciprocal-Proj identification claimed in the manuscript's Theorem
4.2. -/
def affine_presentation_scheme_iso (r : ℕ) (hr : 2 ≤ r) :
    Carlet.Quadratic.openPresentationScheme r ≅
      Carlet.Quadratic.quadraticPresentationScheme r :=
  Carlet.Quadratic.presentationSchemeIso r (by omega)

#print axioms affine_model_points_equiv
#print axioms exists_quadraticPoint_iff_hasZeroSumSubspace
#print axioms prefix_coordinates_linearIndependent
#print axioms prefixCoefficientsEquiv
#print axioms blockSum_eq_prefixSpan_sum
#print axioms manuscript_reciprocal_fiber_eq_quadraticT
#print axioms manuscript_fiber_sum_eq_linearCoefficient_over_delta
#print axioms manuscript_fiber_sum_eq_subspacePolynomial_coefficient_over_delta
#print axioms affine_presentation_scheme_iso

end Carlet.CandidatePaper.Section4
