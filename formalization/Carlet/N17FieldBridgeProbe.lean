import Carlet.Frobenius17Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
lemma f17_monic_bridge : f17.Monic := by unfold f17; monicity <;> norm_num
lemma f17_ne_zero_bridge : f17 ≠ 0 := f17_monic_bridge.ne_zero
lemma f17_natDegree_bridge : f17.natDegree = 17 := by
  have hs : ((X : P17)^3 + 1).natDegree < 17 := by
    calc
      _ ≤ max ((X : P17)^3).natDegree (1 : P17).natDegree := Polynomial.natDegree_add_le _ _
      _ = 3 := by simp
      _ < 17 := by norm_num
  have hp : ((X : P17)^17).natDegree = 17 := Polynomial.natDegree_X_pow 17
  have hs' : ((X : P17)^3 + 1).natDegree < ((X : P17)^17).natDegree := by rw [hp]; exact hs
  unfold f17
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp
@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f17) := by
  let pb := AdjoinRoot.powerBasis' f17_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm
theorem adjoinRoot17_card : Fintype.card (AdjoinRoot f17) = 2^17 := by
  let pb := AdjoinRoot.powerBasis' f17_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f17) = 17 := by
    calc
      Module.finrank F17 (AdjoinRoot f17) = pb.dim := PowerBasis.finrank pb
      _ = f17.natDegree := by simp [pb]
      _ = 17 := f17_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f17), hdim]
#print axioms adjoinRoot17_card


