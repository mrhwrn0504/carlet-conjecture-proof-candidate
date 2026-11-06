import Carlet.Frobenius23Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

open Polynomial
noncomputable section
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩

lemma f23_monic_bridge : f23.Monic := by unfold f23; monicity <;> norm_num
lemma f23_natDegree_bridge : f23.natDegree = 23 := by
  have hs : ((X:P17)^5+1).natDegree < 23 := by
    calc
      _ ≤ max ((X:P17)^5).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
      _ = 5 := by simp
      _ < 23 := by norm_num
  have hp : ((X:P17)^23).natDegree = 23 := Polynomial.natDegree_X_pow 23
  have hs' : ((X:P17)^5+1).natDegree < ((X:P17)^23).natDegree := by rw [hp]; exact hs
  have he : f23 = (X:P17)^23 + ((X:P17)^5+1) := by unfold f23; ring
  rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp

@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f23) := by
  let pb := AdjoinRoot.powerBasis' f23_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm

theorem adjoinRoot23_card : Fintype.card (AdjoinRoot f23) = 2^23 := by
  let pb := AdjoinRoot.powerBasis' f23_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f23) = 23 := by
    calc
      Module.finrank F17 (AdjoinRoot f23) = pb.dim := PowerBasis.finrank pb
      _ = f23.natDegree := by simp [pb]
      _ = 23 := f23_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f23), hdim]

#print axioms adjoinRoot23_card
