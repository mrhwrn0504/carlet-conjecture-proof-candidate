import Carlet.Frobenius25Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

open Polynomial
noncomputable section
local instance : Fact (Irreducible f25) := ⟨f25_irreducible⟩

lemma f25_monic_bridge : f25.Monic := by unfold f25; monicity <;> norm_num
lemma f25_natDegree_bridge : f25.natDegree = 25 := by
  have hs : ((X:P17)^3+1).natDegree < 25 := by
    calc
      _ ≤ max ((X:P17)^3).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
      _ = 3 := by simp
      _ < 25 := by norm_num
  have hp : ((X:P17)^25).natDegree = 25 := Polynomial.natDegree_X_pow 25
  have hs' : ((X:P17)^3+1).natDegree < ((X:P17)^25).natDegree := by rw [hp]; exact hs
  have he : f25 = (X:P17)^25 + ((X:P17)^3+1) := by unfold f25; ring
  rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp

@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f25) := by
  let pb := AdjoinRoot.powerBasis' f25_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm

theorem adjoinRoot25_card : Fintype.card (AdjoinRoot f25) = 2^25 := by
  let pb := AdjoinRoot.powerBasis' f25_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f25) = 25 := by
    calc
      Module.finrank F17 (AdjoinRoot f25) = pb.dim := PowerBasis.finrank pb
      _ = f25.natDegree := by simp [pb]
      _ = 25 := f25_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f25), hdim]

#print axioms adjoinRoot25_card

