import Carlet.ImageBijection
import Carlet.TransferOperator
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

namespace Carlet

def binaryCharacter : AddChar (ZMod 2) ℝ where
  toFun a := if a = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    have hcases (x : ZMod 2) : x = 0 ∨ x = 1 := by
      fin_cases x
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero]

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

attribute [local instance] Classical.propDecidable

local instance (E : Submodule (ZMod 2) K) : Fintype E := Fintype.ofFinite E

def traceCharacter : AddChar K ℝ :=
  binaryCharacter.compAddMonoidHom (Algebra.trace (ZMod 2) K).toAddMonoidHom

theorem traceCharacter_ne_zero : traceCharacter (K := K) ≠ 0 := by
  obtain ⟨x,hx⟩ := Algebra.trace_surjective (ZMod 2) K (1 : ZMod 2)
  intro h
  have hh := congrArg (fun ψ : AddChar K ℝ => ψ x) h
  change binaryCharacter (Algebra.trace (ZMod 2) K x) = 1 at hh
  rw [hx] at hh
  norm_num [binaryCharacter] at hh

omit [Fintype K] in
theorem traceCharacter_eq_one_iff (x : K) :
    traceCharacter x = 1 ↔ Algebra.trace (ZMod 2) K x = 0 := by
  change (if Algebra.trace (ZMod 2) K x = 0 then (1 : ℝ) else -1) = 1 ↔ _
  split_ifs with h
  · simp [h]
  · norm_num [h]

/-- Exact character orthogonality on an actual F₂-subspace. -/
theorem traceCharacter_sum_subspace (E : Submodule (ZMod 2) K) :
    (∑ v : E, traceCharacter (v : K)) =
      if E ≤ LinearMap.ker (Algebra.trace (ZMod 2) K) then (Nat.card E : ℝ) else 0 := by
  classical
  let ψ : AddChar E ℝ := traceCharacter.compAddMonoidHom E.subtype.toAddMonoidHom
  have he : ψ = 0 ↔ E ≤ LinearMap.ker (Algebra.trace (ZMod 2) K) := by
    constructor
    · intro h x hx
      have hh := congrArg (fun φ : AddChar E ℝ => φ ⟨x,hx⟩) h
      exact (traceCharacter_eq_one_iff x).mp hh
    · intro h
      apply AddChar.ext
      intro x
      exact (traceCharacter_eq_one_iff x.val).mpr (h x.property)
  have hs := AddChar.sum_eq_ite ψ
  simpa only [ψ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
    Submodule.coe_subtype, he, Nat.card_eq_fintype_card] using hs

def traceOrthogonal (E : Submodule (ZMod 2) K) : Submodule (ZMod 2) K :=
  (Algebra.traceForm (ZMod 2) K).orthogonal E

theorem traceOrthogonal_involutive : Function.Involutive (traceOrthogonal (K := K)) := by
  intro E
  exact LinearMap.BilinForm.orthogonal_orthogonal
    (traceForm_nondegenerate (ZMod 2) K)
    (Algebra.traceForm_isSymm (ZMod 2) (S := K)).isRefl E

def traceOrthogonalEquiv : Submodule (ZMod 2) K ≃ Submodule (ZMod 2) K :=
  ⟨traceOrthogonal, traceOrthogonal, traceOrthogonal_involutive, traceOrthogonal_involutive⟩

theorem traceOrthogonal_finrank (E : Submodule (ZMod 2) K) :
    Module.finrank (ZMod 2) (traceOrthogonal E) =
      Module.finrank (ZMod 2) K - Module.finrank (ZMod 2) E :=
  LinearMap.BilinForm.finrank_orthogonal (traceForm_nondegenerate (ZMod 2) K) E

variable [DecidableEq K]

def dualImageEquiv : Submodule (ZMod 2) K ≃ Submodule (ZMod 2) K :=
  imageSubspaceEquiv.trans traceOrthogonalEquiv

theorem dualImage_finrank (E : Submodule (ZMod 2) K) :
    Module.finrank (ZMod 2) (dualImageEquiv E) = Module.finrank (ZMod 2) E := by
  change Module.finrank (ZMod 2) (traceOrthogonal (imageSubspace E)) = _
  rw [traceOrthogonal_finrank]
  have h := image_finrank_add E
  omega

#print axioms traceCharacter_ne_zero
#print axioms traceCharacter_sum_subspace
#print axioms traceOrthogonal_involutive
#print axioms dualImageEquiv
#print axioms dualImage_finrank

end Carlet
