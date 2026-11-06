import Carlet.Frobenius9Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
lemma f9_monic_bridge : f9.Monic := by unfold f9; monicity; norm_num
lemma f9_ne_zero_bridge : f9 ≠ 0 := f9_monic_bridge.ne_zero
lemma f9_natDegree_bridge : f9.natDegree = 9 := by
  have hs : ((X : P17)+ 1).natDegree < 9 := by
    calc
      _ ≤ max ((X : P17).natDegree) (1 : P17).natDegree := Polynomial.natDegree_add_le _ _
      _ = 1 := by simp
      _ < 9 := by norm_num
  have hp : ((X : P17)^9).natDegree = 9 := Polynomial.natDegree_X_pow 9
  have hs' : ((X : P17)+ 1).natDegree < ((X : P17)^9).natDegree := by rw [hp]; exact hs
  have he : f9 = (X:P17)^9 + (X+1) := by unfold f9; ring
  rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp
@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f9) := by
  let pb := AdjoinRoot.powerBasis' f9_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm
theorem adjoinRoot9_card : Fintype.card (AdjoinRoot f9) = 2^9 := by
  let pb := AdjoinRoot.powerBasis' f9_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f9) = 9 := by
    calc
      Module.finrank F17 (AdjoinRoot f9) = pb.dim := PowerBasis.finrank pb
      _ = f9.natDegree := by simp [pb]
      _ = 9 := f9_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f9), hdim]
#print axioms adjoinRoot9_card


