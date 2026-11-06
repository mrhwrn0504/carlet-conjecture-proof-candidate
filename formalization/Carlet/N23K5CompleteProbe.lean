import Carlet.N23K5SupportLinearProbe
import Carlet.N23K5InvForTermProbe
import Carlet.N23FieldBridgeProbe
import Carlet.FieldTransport
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩

theorem n23K5SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 5), (n23K5SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 5))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 5), (n23K5SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (n23K5SubsetSum s)⁻¹ := by
      rw [← hp]
    _ = ∑ m : Fin 32, (n23K5SubsetSum (n23K5SubsetDecode m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (n23K5SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 32)), (n23K5SubsetSum (n23K5SubsetDecode m))⁻¹ := by
          apply Finset.sum_equiv n23K5SubsetCodeEquiv
          · intro s
            simp
          · intro s hs
            simpa [n23K5SubsetCodeEquiv] using
              (congrArg (fun x => (n23K5SubsetSum x)⁻¹) (n23K5SubsetCodeDecode_left s)).symm
        _ = ∑ m : Fin 32, (n23K5SubsetSum (n23K5SubsetDecode m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show n23K5SubsetDecode (0 : Fin 32) = ∅ by decide, n23K5SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 31, (n23K5SubsetSum (n23K5SubsetDecode i.succ))⁻¹) =
            ∑ i : Fin 31, n23K5InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact n23K5DecodeInvSucc i
        _ = 0 := n23K5InvFor_sum_zero

theorem n23K5Subspace_isZeroSum : Carlet.IsZeroSum n23K5Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset n23K5Subspace).erase 0, x⁻¹) = 0
  rw [n23K5Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 5))))
      (f := fun s => (n23K5SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 5))) (by simp)
  rw [n23K5SubsetSum_empty, inv_zero, add_zero, n23K5SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_2pow23_five_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f23) 5 :=
  ⟨n23K5Subspace, n23K5Subspace_finrank, n23K5Subspace_isZeroSum⟩

theorem hasZeroSumSubspace_n23_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 23) : Carlet.HasZeroSumSubspace K 5 := by
  have hsrc : Fintype.card (AdjoinRoot f23) = Fintype.card K := by
    rw [adjoinRoot23_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 5 hsrc hasZeroSumSubspace_2pow23_five_probe

#print axioms n23K5SubsetSum_all_inverse_zero
#print axioms n23K5Subspace_isZeroSum
#print axioms hasZeroSumSubspace_2pow23_five_probe
#print axioms hasZeroSumSubspace_n23_card_probe





