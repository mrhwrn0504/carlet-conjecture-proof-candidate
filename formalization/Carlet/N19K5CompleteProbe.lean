import Carlet.N19InvForTerm
import Carlet.N13FieldBridgeProbe
import Carlet.FieldTransport
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩

theorem c19SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 5), (c19SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 5))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 5), (c19SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (c19SubsetSum s)⁻¹ := by
      rw [← hp]
    _ = ∑ m : Fin 32, (c19SubsetSum (subsetDecode19 m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (c19SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 32)), (c19SubsetSum (subsetDecode19 m))⁻¹ := by
          apply Finset.sum_equiv subsetCode19Equiv
          · intro s
            simp
          · intro s hs
            simpa [subsetCode19Equiv] using
              (congrArg (fun x => (c19SubsetSum x)⁻¹) (subsetCode19Decode_left s)).symm
        _ = ∑ m : Fin 32, (c19SubsetSum (subsetDecode19 m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode19 (0 : Fin 32) = ∅ by decide, c19SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 31, (c19SubsetSum (subsetDecode19 i.succ))⁻¹) =
            ∑ i : Fin 31, c19InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact c19DecodeInvSucc i
        _ = 0 := c19InvFor_sum_zero

theorem c19Subspace_isZeroSum_probe : Carlet.IsZeroSum c19Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset c19Subspace).erase 0, x⁻¹) = 0
  rw [c19Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 5))))
      (f := fun s => (c19SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 5))) (by simp)
  rw [c19SubsetSum_empty, inv_zero, add_zero, c19SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_524288_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f19) 5 :=
  ⟨c19Subspace, c19Subspace_finrank, c19Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n19_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 19) : Carlet.HasZeroSumSubspace K 5 := by
  have hsrc : Fintype.card (AdjoinRoot f19) = Fintype.card K := by
    rw [adjoinRoot19_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 5 hsrc hasZeroSumSubspace_524288_probe

#print axioms c19SubsetSum_all_inverse_zero
#print axioms c19Subspace_isZeroSum_probe
#print axioms hasZeroSumSubspace_524288_probe
#print axioms hasZeroSumSubspace_n19_card_probe




