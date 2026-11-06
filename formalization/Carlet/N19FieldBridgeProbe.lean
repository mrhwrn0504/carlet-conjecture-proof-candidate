import Carlet.N19ModulusBridgeProbe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
lemma f19_monic_bridge : f19.Monic := by
  rw [f19_certificate_eq_frobenius]
  unfold f19Frob
  monicity <;> norm_num
lemma f19_ne_zero_bridge : f19 ≠ 0 := f19_monic_bridge.ne_zero
lemma f19_natDegree_bridge : f19.natDegree = 19 := by
  have hd : f19Frob.natDegree = 19 := by
    have hplus : ((X:P19Frob)+1).natDegree ≤ 1 := by
      calc
        _ ≤ max (X:P19Frob).natDegree (1:P19Frob).natDegree := Polynomial.natDegree_add_le _ _
        _ = 1 := by simp
    have h2 : ((X:P19Frob)^2+((X:P19Frob)+1)).natDegree ≤ 2 := by
      calc
        _ ≤ max ((X:P19Frob)^2).natDegree ((X:P19Frob)+1).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by simp only [Polynomial.natDegree_X_pow]; omega
    have hlow : ((X:P19Frob)^5+((X:P19Frob)^2+((X:P19Frob)+1))).natDegree ≤ 5 := by
      calc
        _ ≤ max ((X:P19Frob)^5).natDegree ((X:P19Frob)^2+((X:P19Frob)+1)).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 5 := by simp only [Polynomial.natDegree_X_pow]; omega
    have hp:((X:P19Frob)^19).natDegree=19 := Polynomial.natDegree_X_pow 19
    have hs':((X:P19Frob)^5+((X:P19Frob)^2+((X:P19Frob)+1))).natDegree<((X:P19Frob)^19).natDegree := by rw [hp]; omega
    unfold f19Frob; rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']; exact hp
  rw [f19_certificate_eq_frobenius]
  exact hd
@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f19) := by
  let pb := AdjoinRoot.powerBasis' f19_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm
theorem adjoinRoot19_card : Fintype.card (AdjoinRoot f19) = 2^19 := by
  let pb := AdjoinRoot.powerBasis' f19_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f19) = 19 := by
    calc
      Module.finrank F17 (AdjoinRoot f19) = pb.dim := PowerBasis.finrank pb
      _ = f19.natDegree := by simp [pb]
      _ = 19 := f19_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f19), hdim]
#print axioms adjoinRoot19_card


