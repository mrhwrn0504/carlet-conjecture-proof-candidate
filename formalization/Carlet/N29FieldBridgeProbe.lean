import Carlet.Frobenius29Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

open Polynomial
noncomputable section
local instance : Fact (Irreducible f29) := ⟨f29_irreducible⟩

lemma f29_monic_bridge : f29.Monic := by unfold f29; monicity <;> norm_num
lemma f29_natDegree_bridge : f29.natDegree = 29 := by
  have hs : ((X:P17)^2+1).natDegree < 29 := by
    calc
      _ ≤ max ((X:P17)^2).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
      _ = 2 := by simp
      _ < 29 := by norm_num
  have hp : ((X:P17)^29).natDegree = 29 := Polynomial.natDegree_X_pow 29
  have hs' : ((X:P17)^2+1).natDegree < ((X:P17)^29).natDegree := by rw [hp]; exact hs
  have he : f29 = (X:P17)^29 + ((X:P17)^2+1) := by unfold f29; ring
  rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp

@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f29) := by
  let pb := AdjoinRoot.powerBasis' f29_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm

theorem adjoinRoot29_card : Fintype.card (AdjoinRoot f29) = 2^29 := by
  let pb := AdjoinRoot.powerBasis' f29_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f29) = 29 := by
    calc
      Module.finrank F17 (AdjoinRoot f29) = pb.dim := PowerBasis.finrank pb
      _ = f29.natDegree := by simp [pb]
      _ = 29 := f29_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f29), hdim]

#print axioms adjoinRoot29_card


