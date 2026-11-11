import Carlet.CandidatePaper.Section32CoordinateSplit
import Carlet.FrobeniusCoefficients
import Carlet.CandidatePaper.RationalFunctionLogDerivative
import Carlet.CandidatePaper.Section32SubspaceDerivative
import Carlet.CandidatePaper.Section32Nonvanishing
import Carlet.SubspacePolynomial
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section

namespace Carlet.CandidatePaper.Section32InfiniteFiber

open Polynomial

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

local instance : DecidableEq K := Classical.decEq K

/-- The root product indexed by every binary linear combination of a tuple.
The definition does not assume that the tuple is independent. -/
def binaryRootProduct {r : ℕ} (x : Fin r → K) : K[X] :=
  ∏ v : Fin r → ZMod 2, (X + C (Section32CoordinateSplit.binaryLinearForm x v))

omit [Algebra (ZMod 2) K] in
theorem fintype_prod_comp (ι : Type*) [Fintype ι] (f : ι → K[X]) (q : K[X]) :
    (∏ i : ι, f i).comp q = ∏ i : ι, (f i).comp q := by
  simpa using (Polynomial.prod_comp (Finset.univ : Finset ι) f q)

theorem binaryRootProduct_lastCases {r : ℕ} (x : Fin r → K) (t : K) :
    binaryRootProduct (Fin.lastCases t x) =
      binaryRootProduct x * (binaryRootProduct x).comp (X + C t) := by
  classical
  unfold binaryRootProduct
  calc
    (∏ v : Fin (r + 1) → ZMod 2,
        (X + C (Section32CoordinateSplit.binaryLinearForm (Fin.lastCases t x) v))) =
      ∏ p : (Fin r → ZMod 2) × ZMod 2,
        (X + C (Section32CoordinateSplit.binaryLinearForm (Fin.lastCases t x)
          ((Section32CoordinateSplit.coefficientSplitEquiv r).symm p))) := by
            apply Fintype.prod_equiv (Section32CoordinateSplit.coefficientSplitEquiv r)
            intro v
            simp
    _ = ∏ u : Fin r → ZMod 2, ∏ b : ZMod 2,
        (X + C (Section32CoordinateSplit.binaryLinearForm (Fin.lastCases t x)
          ((Section32CoordinateSplit.coefficientSplitEquiv r).symm (u, b)))) :=
            by rw [Fintype.prod_prod_type]
    _ = ∏ u : Fin r → ZMod 2,
        ((X + C (Section32CoordinateSplit.binaryLinearForm x u)) *
         (X + C (Section32CoordinateSplit.binaryLinearForm x u + t))) := by
            apply Fintype.prod_congr
            intro u
            have hbinary : (Finset.univ : Finset (ZMod 2)) = insert 0 {1} := by decide
            rw [hbinary, Finset.prod_insert]
            · simp only [Finset.prod_singleton]
              simp [Section32CoordinateSplit.binaryLinearForm_lastCases, add_comm]
            · simp
    _ = (∏ u : Fin r → ZMod 2,
          (X + C (Section32CoordinateSplit.binaryLinearForm x u))) *
        (∏ u : Fin r → ZMod 2,
          (X + C (Section32CoordinateSplit.binaryLinearForm x u + t))) := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ u : Fin r → ZMod 2,
          (X + C (Section32CoordinateSplit.binaryLinearForm x u))) *
        ((∏ u : Fin r → ZMod 2,
          (X + C (Section32CoordinateSplit.binaryLinearForm x u))).comp (X + C t)) := by
            have hcomp :
                (∏ u : Fin r → ZMod 2,
                  (X + C (Section32CoordinateSplit.binaryLinearForm x u + t))) =
                (∏ u : Fin r → ZMod 2,
                  (X + C (Section32CoordinateSplit.binaryLinearForm x u))).comp (X + C t) := by
              calc
                _ = ∏ u : Fin r → ZMod 2,
                    (X + C (Section32CoordinateSplit.binaryLinearForm x u)).comp (X + C t) := by
                      apply Fintype.prod_congr
                      intro u
                      simp [add_comm, add_left_comm]
                _ = _ := (fintype_prod_comp (Fin r → ZMod 2)
                  (fun u => X + C (Section32CoordinateSplit.binaryLinearForm x u)) (X + C t)).symm
            exact congrArg (fun q : K[X] =>
              (∏ u : Fin r → ZMod 2,
                (X + C (Section32CoordinateSplit.binaryLinearForm x u))) * q) hcomp
    _ = binaryRootProduct x * (binaryRootProduct x).comp (X + C t) := by
            rfl

/-- If the previous coordinate root polynomial is additive, adjoining one
more coordinate gives the usual linearized-polynomial recurrence. -/
theorem binaryRootProduct_lastCases_recurrence {r : ℕ} (x : Fin r → K) (t : K)
    (htrans : Carlet.HasTranslationIdentity (binaryRootProduct x)) :
    binaryRootProduct (Fin.lastCases t x) =
      (binaryRootProduct x)^2 +
        C ((binaryRootProduct x).eval t) * binaryRootProduct x := by
  rw [binaryRootProduct_lastCases, htrans t]
  ring

/-- Translation identity is preserved when one binary coordinate is adjoined. -/
theorem binaryRootProduct_lastCases_translation {r : ℕ} (x : Fin r → K) (t : K)
    (htrans : Carlet.HasTranslationIdentity (binaryRootProduct x)) :
    Carlet.HasTranslationIdentity (binaryRootProduct (Fin.lastCases t x)) := by
  rw [binaryRootProduct_lastCases_recurrence x t htrans]
  exact Carlet.translationIdentity_step _ _ htrans

/-- The root polynomial of every finite binary coordinate tuple is additive.
This works over an arbitrary characteristic-two field, including infinite
rational-function fields. -/
theorem binaryRootProduct_translation (r : ℕ) (x : Fin r → K) :
    Carlet.HasTranslationIdentity (binaryRootProduct x) := by
  induction r with
  | zero =>
      have hx : x = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst x
      have hpoly : binaryRootProduct (fun i : Fin 0 => (Fin.elim0 i : K)) =
          (X : K[X]) := by
        simp [binaryRootProduct, Section32CoordinateSplit.binaryLinearForm]
      rw [hpoly]
      exact Carlet.translationIdentity_X
  | succ r ih =>
      let y : Fin r → K := fun i => x i.castSucc
      let t : K := x (Fin.last r)
      have hxy : Fin.lastCases t y = x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [t]
        · simp [y]
      rw [← hxy]
      exact binaryRootProduct_lastCases_translation y t (ih y)

omit [Algebra (ZMod 2) K] in
theorem frobeniusSupported_add {p q : K[X]}
    (hp : Carlet.FrobeniusSupported p) (hq : Carlet.FrobeniusSupported q) :
    Carlet.FrobeniusSupported (p + q) := by
  intro i hi
  rw [Polynomial.coeff_add] at hi
  by_cases hpz : p.coeff i ≠ 0
  · exact hp i hpz
  · have hqz : q.coeff i ≠ 0 := by
      intro hqz
      have hp0 : p.coeff i = 0 := not_ne_iff.mp hpz
      apply hi
      rw [hp0, hqz]
      simp
    exact hq i hqz

omit [Algebra (ZMod 2) K] in
theorem frobeniusSupported_C_mul {p : K[X]} (c : K)
    (hp : Carlet.FrobeniusSupported p) :
    Carlet.FrobeniusSupported (C c * p) := by
  intro i hi
  rw [Polynomial.coeff_C_mul] at hi
  have hpz : p.coeff i ≠ 0 := by
    intro h
    apply hi
    simp [h]
  exact hp i hpz

/-- The root product has only Frobenius-power exponents in characteristic two.
This extends the finite-ambient-field support argument to arbitrary fields. -/
theorem binaryRootProduct_frobeniusSupported (r : ℕ) (x : Fin r → K) :
    Carlet.FrobeniusSupported (binaryRootProduct x) := by
  induction r with
  | zero =>
      have hx : x = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst x
      intro i hi
      have hpoly : binaryRootProduct (fun i : Fin 0 => (Fin.elim0 i : K)) =
          (X : K[X]) := by
        simp [binaryRootProduct, Section32CoordinateSplit.binaryLinearForm]
      rw [hpoly] at hi
      by_cases h : i = 1
      · refine ⟨0, ?_⟩
        rw [h]
        norm_num
      · simp [Polynomial.coeff_X] at hi
        exact False.elim (h hi.symm)
  | succ r ih =>
      let y : Fin r → K := fun i => x i.castSucc
      let t : K := x (Fin.last r)
      have hxy : Fin.lastCases t y = x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [t]
        · simp [y]
      rw [← hxy, binaryRootProduct_lastCases_recurrence y t
        (binaryRootProduct_translation r y)]
      apply frobeniusSupported_add
      · exact Carlet.frobeniusSupported_square (ih y)
      · exact frobeniusSupported_C_mul _ (ih y)

/-- For independent coordinates, the indexed product has no repeated roots,
so it is the ordinary root product of their finite binary span. -/
theorem binaryRootProduct_eq_rootProduct_image {r : ℕ} (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) :
    binaryRootProduct x =
      Carlet.rootProduct (Finset.univ.image (Section32CoordinateSplit.binaryLinearForm x)) := by
  classical
  unfold binaryRootProduct Carlet.rootProduct
  have hinj : Set.InjOn (Section32CoordinateSplit.binaryLinearForm x)
      (↑(Finset.univ : Finset (Fin r → ZMod 2))) := by
    intro a ha b hb hab
    exact Section32CoordinateSplit.binaryLinearForm_injective x hli hab
  rw [Finset.prod_image hinj]

/-- The linear coefficient is nonzero for an independent coordinate tuple. -/
theorem binaryRootProduct_coeff_one_ne {r : ℕ} (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) :
    (binaryRootProduct x).coeff 1 ≠ 0 := by
  classical
  let s := Finset.univ.image (Section32CoordinateSplit.binaryLinearForm x)
  have hzero : (0 : K) ∈ s := by
    refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
    simp [Section32CoordinateSplit.binaryLinearForm]
  rw [binaryRootProduct_eq_rootProduct_image x hli]
  rw [Carlet.rootProduct_eq_X_mul_nonzeroRootProduct s hzero]
  simpa [Polynomial.coeff_X_mul] using Carlet.nonzeroRootProduct_coeff_zero_ne s

/-- The derivative of the span root polynomial is a nonzero constant. -/
theorem binaryRootProduct_derivative_eq_C {r : ℕ} (x : Fin r → K) :
    (binaryRootProduct x).derivative = C ((binaryRootProduct x).coeff 1) := by
  exact Carlet.CandidatePaper.Section32SubspaceDerivative.derivative_eq_C_coeff_one_of_frobeniusSupported
    (binaryRootProduct x)
    (binaryRootProduct_frobeniusSupported r x)

theorem binaryRootProduct_derivative_ne_zero {r : ℕ} (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) :
    (binaryRootProduct x).derivative ≠ 0 := by
  rw [binaryRootProduct_derivative_eq_C x]
  exact Polynomial.C_ne_zero.mpr (binaryRootProduct_coeff_one_ne x hli)

/-- The fiber sum over binary linear forms equals the sum over their distinct
values in the coefficient field's finite subset. -/
theorem binaryFiber_reciprocal_sum_eq_image {r : ℕ} (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) :
    (∑ u : Fin r → ZMod 2,
      (algebraMap K[X] (FractionRing K[X])
        (X + C (Section32CoordinateSplit.binaryLinearForm x u)))⁻¹) =
      ∑ a ∈ Finset.univ.image (Section32CoordinateSplit.binaryLinearForm x),
        (algebraMap K[X] (FractionRing K[X]) (X + C a))⁻¹ := by
  classical
  have hinj : Set.InjOn (Section32CoordinateSplit.binaryLinearForm x)
      (↑(Finset.univ : Finset (Fin r → ZMod 2))) := by
    intro a ha b hb hab
    exact Section32CoordinateSplit.binaryLinearForm_injective x hli hab
  symm
  exact Finset.sum_image hinj

/-- A nonzero previous-dimensional value cannot be canceled by the new
coordinate fiber. This is the universal rational-function nonvanishing hinge
of the candidate paper's Section 3.2. -/
theorem binaryFiber_add_nonzero {r : ℕ} (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) (c : K) (hc : c ≠ 0) :
    algebraMap K[X] (FractionRing K[X]) (C c) +
      ∑ u : Fin r → ZMod 2,
        (algebraMap K[X] (FractionRing K[X])
          (X + C (Section32CoordinateSplit.binaryLinearForm x u)))⁻¹ ≠ 0 := by
  rw [binaryFiber_reciprocal_sum_eq_image x hli]
  exact Carlet.CandidatePaper.Section32Nonvanishing.nonzero_constant_add_fiber_reciprocal_sum
      (Finset.univ.image (Section32CoordinateSplit.binaryLinearForm x)) c hc

/-- The scalar extension map is linear over the common prime field. -/
noncomputable def algebraMapF2Linear {L : Type*} [Field L]
    [Algebra (ZMod 2) L] [Algebra K L] [IsScalarTower (ZMod 2) K L] :
    K →ₗ[ZMod 2] L where
  toFun := algebraMap K L
  map_add' := by
    intro x y
    exact map_add (algebraMap K L) x y
  map_smul' := by
    intro a x
    calc
      algebraMap K L (a • x) =
          algebraMap K L ((algebraMap (ZMod 2) K a) * x) := by
            rw [Algebra.smul_def]
      _ = algebraMap K L (algebraMap (ZMod 2) K a) * algebraMap K L x :=
            map_mul (algebraMap K L) _ _
      _ = algebraMap (ZMod 2) L a * algebraMap K L x := by
            rw [← IsScalarTower.algebraMap_apply]
      _ = a • algebraMap K L x := by rw [Algebra.smul_def]

/-- Binary linear forms commute with embeddings of characteristic-two fields. -/
theorem binaryLinearForm_algebraMap {L : Type*} [Field L]
    [Algebra (ZMod 2) L] [Algebra K L] [IsScalarTower (ZMod 2) K L]
    {r : ℕ} (x : Fin r → K) (v : Fin r → ZMod 2) :
    Section32CoordinateSplit.binaryLinearForm
        (fun i => algebraMap K L (x i)) v =
      algebraMap K L (Section32CoordinateSplit.binaryLinearForm x v) := by
  change (∑ i : Fin r, v i • algebraMap K L (x i)) =
    algebraMapF2Linear (∑ i : Fin r, v i • x i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (LinearMap.map_smul (algebraMapF2Linear (K := K) (L := L))
    (v i) (x i)).symm

/-- The reciprocal sum is preserved by a prime-field-compatible embedding. -/
theorem binaryReciprocalSum_algebraMap {L : Type*} [Field L]
    [Algebra (ZMod 2) L] [Algebra K L] [IsScalarTower (ZMod 2) K L]
    {r : ℕ} (x : Fin r → K) :
    algebraMap K L (Section32CoordinateSplit.binaryReciprocalSum x) =
      Section32CoordinateSplit.binaryReciprocalSum (fun i => algebraMap K L (x i)) := by
  classical
  unfold Section32CoordinateSplit.binaryReciprocalSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [binaryLinearForm_algebraMap]
  simp

#print axioms binaryRootProduct_lastCases
#print axioms binaryRootProduct_lastCases_recurrence
#print axioms binaryRootProduct_lastCases_translation
#print axioms binaryRootProduct_translation
#print axioms binaryRootProduct_frobeniusSupported
#print axioms binaryRootProduct_eq_rootProduct_image
#print axioms binaryRootProduct_coeff_one_ne
#print axioms binaryRootProduct_derivative_eq_C
#print axioms binaryRootProduct_derivative_ne_zero
#print axioms binaryFiber_reciprocal_sum_eq_image
#print axioms binaryFiber_add_nonzero
#print axioms algebraMapF2Linear
#print axioms binaryLinearForm_algebraMap
#print axioms binaryReciprocalSum_algebraMap

end Carlet.CandidatePaper.Section32InfiniteFiber
