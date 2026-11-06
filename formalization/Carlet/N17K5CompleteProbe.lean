import Carlet.N17InvForTerm
import Carlet.N13FieldBridgeProbe
import Carlet.FieldTransport
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩

theorem c17SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 5), (c17SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 5))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 5), (c17SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (c17SubsetSum s)⁻¹ := by
      rw [← hp]
    _ = ∑ m : Fin 32, (c17SubsetSum (subsetDecode17 m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (c17SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 32)), (c17SubsetSum (subsetDecode17 m))⁻¹ := by
          apply Finset.sum_equiv subsetCode17Equiv
          · intro s
            simp
          · intro s hs
            simpa [subsetCode17Equiv] using
              (congrArg (fun x => (c17SubsetSum x)⁻¹) (subsetCode17Decode_left s)).symm
        _ = ∑ m : Fin 32, (c17SubsetSum (subsetDecode17 m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode17 (0 : Fin 32) = ∅ by decide, c17SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 31, (c17SubsetSum (subsetDecode17 i.succ))⁻¹) =
            ∑ i : Fin 31, c17InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact c17DecodeInvSucc i
        _ = 0 := c17InvFor_sum_zero

theorem c17Subspace_isZeroSum_probe : Carlet.IsZeroSum c17Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset c17Subspace).erase 0, x⁻¹) = 0
  rw [c17Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 5))))
      (f := fun s => (c17SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 5))) (by simp)
  rw [c17SubsetSum_empty, inv_zero, add_zero, c17SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_131072_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f17) 5 :=
  ⟨c17Subspace, c17Subspace_finrank, c17Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n17_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 17) : Carlet.HasZeroSumSubspace K 5 := by
  have hsrc : Fintype.card (AdjoinRoot f17) = Fintype.card K := by
    rw [adjoinRoot17_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 5 hsrc hasZeroSumSubspace_131072_probe

#print axioms c17SubsetSum_all_inverse_zero
#print axioms c17Subspace_isZeroSum_probe
#print axioms hasZeroSumSubspace_131072_probe
#print axioms hasZeroSumSubspace_n17_card_probe




