import Carlet.Frobenius11Scratch
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
lemma f_monic_bridge : f.Monic := by unfold f; monicity <;> norm_num
lemma f_ne_zero_bridge : f ≠ 0 := f_monic_bridge.ne_zero
lemma f_natDegree_bridge : f.natDegree = 11 := by
  unfold f
  rw [add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 11
  · have hsmall : (X : P)^2 + 1 = (X : P)^2 + C (1:F) := by simp
    rw [hsmall, Polynomial.natDegree_X_pow_add_C, Polynomial.natDegree_X_pow]
    norm_num

@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f) := by
  let pb := AdjoinRoot.powerBasis' f_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm

theorem adjoinRoot11_card : Fintype.card (AdjoinRoot f) = 2^11 := by
  let pb := AdjoinRoot.powerBasis' f_monic_bridge
  have hdim : Module.finrank F (AdjoinRoot f) = 11 := by
    calc
      Module.finrank F (AdjoinRoot f) = pb.dim := PowerBasis.finrank pb
      _ = f.natDegree := by simp [pb]
      _ = 11 := f_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f), hdim]
#print axioms adjoinRoot11_card
#print axioms f_irreducible






