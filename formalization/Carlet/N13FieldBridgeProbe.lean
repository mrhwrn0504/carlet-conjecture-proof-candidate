import Carlet.Frobenius13Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
lemma f13_monic_bridge : f13.Monic := by unfold f13; monicity <;> norm_num
lemma f13_ne_zero_bridge : f13 ≠ 0 := f13_monic_bridge.ne_zero
lemma f13_natDegree_bridge : f13.natDegree = 13 := by
  have h1 : (X : P13).natDegree = 1 := Polynomial.natDegree_X
  have hplus : (X + (1 : P13)).natDegree ≤ 1 := by
    calc
      _ ≤ max (X : P13).natDegree (1 : P13).natDegree := Polynomial.natDegree_add_le _ _
      _ = 1 := by simp [h1]
  have h3 : ((X : P13)^3 + (X + 1)).natDegree ≤ 3 := by
    calc
      _ ≤ max ((X : P13)^3).natDegree (X + 1).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 3 := by simp only [Polynomial.natDegree_X_pow]; omega
  have h4 : ((X : P13)^4 + (X^3 + (X + 1))).natDegree ≤ 4 := by
    calc
      _ ≤ max ((X : P13)^4).natDegree (X^3 + (X + 1)).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 4 := by simp only [Polynomial.natDegree_X_pow]; omega
  have hs : ((X : P13)^4 + (X^3 + (X + 1))).natDegree < 13 := by omega
  have hp : ((X : P13)^13).natDegree = 13 := Polynomial.natDegree_X_pow 13
  have hs' : ((X : P13)^4 + (X^3 + (X + 1))).natDegree < ((X : P13)^13).natDegree := by rw [hp]; exact hs
  unfold f13
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp
@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f13) := by
  let pb := AdjoinRoot.powerBasis' f13_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F13) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm
theorem adjoinRoot13_card : Fintype.card (AdjoinRoot f13) = 2^13 := by
  let pb := AdjoinRoot.powerBasis' f13_monic_bridge
  have hdim : Module.finrank F13 (AdjoinRoot f13) = 13 := by
    calc
      Module.finrank F13 (AdjoinRoot f13) = pb.dim := PowerBasis.finrank pb
      _ = f13.natDegree := by simp [pb]
      _ = 13 := f13_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f13), hdim]
#print axioms adjoinRoot13_card


