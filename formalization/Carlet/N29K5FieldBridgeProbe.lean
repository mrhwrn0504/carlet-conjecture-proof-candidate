import Carlet.Frobenius29K5Probe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

open Polynomial
namespace Carlet
noncomputable section
local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩

lemma f29K5_monic_bridge : f29K5.Monic := by unfold f29K5; monicity <;> norm_num
lemma f29K5_natDegree_bridge : f29K5.natDegree = 29 := by
  have hp : ((X:P17)^29).natDegree = 29 := Polynomial.natDegree_X_pow 29
  have hs : (f29K5 - (X:P17)^29).natDegree ≤ 27 := by
    have hform : f29K5 - (X:P17)^29 = X^27 + X^24 + X^21 + X^19 + X^18 + X^17 + X^14 + X^13 + X^12 + X^6 + X^3 + X^2 + X^1 + 1 := by unfold f29K5; ring_nf
    rw [hform, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN27 : N ≠ 27 := by omega
    have hN24 : N ≠ 24 := by omega
    have hN21 : N ≠ 21 := by omega
    have hN19 : N ≠ 19 := by omega
    have hN18 : N ≠ 18 := by omega
    have hN17 : N ≠ 17 := by omega
    have hN14 : N ≠ 14 := by omega
    have hN13 : N ≠ 13 := by omega
    have hN12 : N ≠ 12 := by omega
    have hN6 : N ≠ 6 := by omega
    have hN3 : N ≠ 3 := by omega
    have hN2 : N ≠ 2 := by omega
    have hN1 : N ≠ 1 := by omega
    have hN0 : N ≠ 0 := by omega
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X, hN27, hN24, hN21, hN19, hN18, hN17, hN14, hN13, hN12, hN6, hN3, hN2, hN0, hN1.symm]
  have hlt : (f29K5 - (X:P17)^29).natDegree < ((X:P17)^29).natDegree := by rw [hp]; omega
  have he : f29K5 = (X:P17)^29 + (f29K5 - (X:P17)^29) := by ring
  rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hp]
@[instance_reducible]
noncomputable instance : Fintype (AdjoinRoot f29K5) := by
  let pb := AdjoinRoot.powerBasis' f29K5_monic_bridge
  letI : Fintype (Fin pb.dim →₀ F17) := Finsupp.fintype
  exact Fintype.ofEquiv _ pb.basis.repr.toEquiv.symm

theorem adjoinRoot29K5_card : Fintype.card (AdjoinRoot f29K5) = 2^29 := by
  let pb := AdjoinRoot.powerBasis' f29K5_monic_bridge
  have hdim : Module.finrank F17 (AdjoinRoot f29K5) = 29 := by
    calc
      Module.finrank F17 (AdjoinRoot f29K5) = pb.dim := PowerBasis.finrank pb
      _ = f29K5.natDegree := by simp [pb]
      _ = 29 := f29K5_natDegree_bridge
  rw [← FiniteField.pow_finrank_eq_card 2 (AdjoinRoot f29K5), hdim]

#print axioms adjoinRoot29K5_card



end
end Carlet
