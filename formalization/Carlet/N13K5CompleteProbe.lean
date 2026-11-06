import Carlet.N13InvForTerm
import Carlet.N13FieldBridgeProbe
import Carlet.FieldTransport
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩

theorem cert13SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 5), (cert13SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 5))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 5), (cert13SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (cert13SubsetSum s)⁻¹ := by
      rw [← hp]
    _ = ∑ m : Fin 32, (cert13SubsetSum (subsetDecode13 m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (cert13SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 32)), (cert13SubsetSum (subsetDecode13 m))⁻¹ := by
          apply Finset.sum_equiv subsetCode13Equiv
          · intro s
            simp
          · intro s hs
            simpa [subsetCode13Equiv] using
              (congrArg (fun x => (cert13SubsetSum x)⁻¹) (subsetCode13Decode_left s)).symm
        _ = ∑ m : Fin 32, (cert13SubsetSum (subsetDecode13 m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode13 (0 : Fin 32) = ∅ by decide, cert13SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 31, (cert13SubsetSum (subsetDecode13 i.succ))⁻¹) =
            ∑ i : Fin 31, cert13InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact cert13DecodeInvSucc i
        _ = 0 := cert13InvFor_sum_zero

theorem cert13Subspace_isZeroSum_probe : Carlet.IsZeroSum cert13Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset cert13Subspace).erase 0, x⁻¹) = 0
  rw [cert13Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 5))))
      (f := fun s => (cert13SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 5))) (by simp)
  rw [cert13SubsetSum_empty, inv_zero, add_zero, cert13SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_8192_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f13) 5 :=
  ⟨cert13Subspace, cert13Subspace_finrank, cert13Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n13_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 13) : Carlet.HasZeroSumSubspace K 5 := by
  have hsrc : Fintype.card (AdjoinRoot f13) = Fintype.card K := by
    rw [adjoinRoot13_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 5 hsrc hasZeroSumSubspace_8192_probe

#print axioms cert13SubsetSum_all_inverse_zero
#print axioms cert13Subspace_isZeroSum_probe
#print axioms hasZeroSumSubspace_8192_probe
#print axioms hasZeroSumSubspace_n13_card_probe




