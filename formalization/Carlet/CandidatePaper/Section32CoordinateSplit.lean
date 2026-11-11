import Carlet.Elementary
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
This file formalizes the finite-sum coordinate split used in the candidate
paper's Section 3.2. It is deliberately stated over an arbitrary field; the
remaining work is to identify its finite family with the generic fiber inside
the universal rational-function field.
-/

noncomputable section

namespace Carlet.CandidatePaper.Section32CoordinateSplit

open scoped BigOperators

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

/-- The coefficient vectors in dimension `r+1`, split into a prefix and the
last binary coefficient. -/
def coefficientSplitEquiv (r : ℕ) :
    (Fin (r + 1) → ZMod 2) ≃ ((Fin r → ZMod 2) × ZMod 2) where
  toFun v := (fun i => v i.castSucc, v (Fin.last r))
  invFun p := Fin.lastCases p.2 p.1
  left_inv v := by
    funext i
    change Fin.lastCases (v (Fin.last r)) (fun j => v j.castSucc) i = v i
    refine Fin.lastCases ?_ (fun _ => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]
  right_inv p := by
    rcases p with ⟨u, b⟩
    apply Prod.ext
    · funext i
      change Fin.lastCases b u i.castSucc = u i
      simp only [Fin.lastCases_castSucc]
    · change Fin.lastCases b u (Fin.last r) = b
      simp only [Fin.lastCases_last]

/-- The linear form on the extended coordinate tuple splits into the prefix
linear form plus the final binary coefficient times the new coordinate. -/
def binaryLinearForm {r : ℕ} (x : Fin r → K)
    (v : Fin r → ZMod 2) : K :=
  ∑ i, v i • x i

theorem binaryLinearForm_lastCases {r : ℕ} (x : Fin r → K) (t : K)
    (u : Fin r → ZMod 2) (b : ZMod 2) :
    binaryLinearForm (Fin.lastCases t x)
        ((coefficientSplitEquiv r).symm (u, b)) =
      binaryLinearForm x u + b • t := by
  dsimp [coefficientSplitEquiv, binaryLinearForm]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

/-- Reciprocal sum over every binary coefficient vector. The zero vector
contributes zero, so this is also the sum over nonzero vectors. -/
def binaryReciprocalSum {r : ℕ} (x : Fin r → K) : K :=
  ∑ v : Fin r → ZMod 2, (binaryLinearForm x v)⁻¹

/-- The zero coefficient vector contributes zero, so the all-vector sum is the
same as the manuscript's sum over nonzero linear forms. -/
theorem binaryReciprocalSum_eq_sum_nonzero {r : ℕ} (x : Fin r → K) :
    binaryReciprocalSum x =
      ∑ v ∈ (Finset.univ : Finset (Fin r → ZMod 2)).erase 0,
        (binaryLinearForm x v)⁻¹ := by
  classical
  unfold binaryReciprocalSum
  rw [← Finset.sum_erase_add Finset.univ
    (fun v : Fin r → ZMod 2 => (binaryLinearForm x v)⁻¹)
    (Finset.mem_univ 0)]
  simp [binaryLinearForm]

/-- Exact splitting identity: the next reciprocal sum is the previous sum plus
the reciprocal sum over the last-coordinate fiber. -/
theorem binaryReciprocalSum_lastCases {r : ℕ} (x : Fin r → K) (t : K) :
    binaryReciprocalSum (Fin.lastCases t x) =
      binaryReciprocalSum x +
        ∑ u : Fin r → ZMod 2, (t + binaryLinearForm x u)⁻¹ := by
  classical
  unfold binaryReciprocalSum
  calc
    (∑ v : Fin (r + 1) → ZMod 2,
        (binaryLinearForm (Fin.lastCases t x) v)⁻¹) =
      ∑ p : (Fin r → ZMod 2) × ZMod 2,
        (binaryLinearForm (Fin.lastCases t x)
          ((coefficientSplitEquiv r).symm p))⁻¹ := by
            apply Fintype.sum_equiv (coefficientSplitEquiv r)
            intro v
            simp
    _ = ∑ u : Fin r → ZMod 2, ∑ b : ZMod 2,
        (binaryLinearForm (Fin.lastCases t x)
          ((coefficientSplitEquiv r).symm (u, b)))⁻¹ :=
            Fintype.sum_prod_type _
    _ = ∑ u : Fin r → ZMod 2,
        ((binaryLinearForm x u)⁻¹ +
          (t + binaryLinearForm x u)⁻¹) := by
            apply Fintype.sum_congr
            intro u
            have hbinary : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
            simp [hbinary, binaryLinearForm_lastCases, add_comm]
    _ = binaryReciprocalSum x +
        ∑ u : Fin r → ZMod 2, (t + binaryLinearForm x u)⁻¹ := by
          simp [binaryReciprocalSum, Finset.sum_add_distrib]

/-- A linearly independent coordinate tuple gives distinct values for all
binary linear forms. -/
theorem binaryLinearForm_injective {r : ℕ} (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) :
    Function.Injective (binaryLinearForm x) := by
  intro v w hvw
  apply funext
  have hsum : ∑ i, (v i - w i) • x i = 0 := by
    calc
      ∑ i, (v i - w i) • x i = ∑ i, (v i • x i - w i • x i) := by
        apply Fintype.sum_congr
        intro i
        rw [sub_smul]
      _ = (∑ i, v i • x i) - ∑ i, w i • x i := by
        exact Finset.sum_sub_distrib _ _
      _ = 0 := sub_eq_zero.mpr hvw
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (v - w) hsum
  intro i
  exact sub_eq_zero.mp (hcoeff i)

/-- For an independent tuple, summing over coefficient vectors agrees with
summing over the finite set of distinct linear-form values. -/
theorem fiber_reciprocal_sum_eq_image {r : ℕ} [DecidableEq K]
    {L : Type*} [Field L] [Algebra K L] (x : Fin r → K)
    (hli : LinearIndependent (ZMod 2) x) (t : L) :
    (∑ u : Fin r → ZMod 2,
        (t + algebraMap K L (binaryLinearForm x u))⁻¹) =
      ∑ a ∈ Finset.univ.image (binaryLinearForm x),
        (t + algebraMap K L a)⁻¹ := by
  classical
  have hinj : Set.InjOn (binaryLinearForm x) (↑(Finset.univ : Finset (Fin r → ZMod 2))) := by
    intro a ha b hb hab
    exact binaryLinearForm_injective x hli hab
  rw [Finset.sum_image hinj]

#print axioms binaryLinearForm_lastCases
#print axioms binaryReciprocalSum_eq_sum_nonzero
#print axioms binaryReciprocalSum_lastCases
#print axioms binaryLinearForm_injective
#print axioms fiber_reciprocal_sum_eq_image

end Carlet.CandidatePaper.Section32CoordinateSplit
