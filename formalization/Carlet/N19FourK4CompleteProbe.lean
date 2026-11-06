import Carlet.N19FourInvForTerm
import Carlet.FieldTransport
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩

theorem e19SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 4), (e19SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 4))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 4), (e19SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (e19SubsetSum s)⁻¹ := by rw [← hp]
    _ = ∑ m : Fin 16, (e19SubsetSum (subsetDecode19Four m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (e19SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 16)), (e19SubsetSum (subsetDecode19Four m))⁻¹ := by
          apply Finset.sum_equiv subsetCode19FourEquiv
          · intro s; simp
          · intro s hs
            simpa [subsetCode19FourEquiv] using
              (congrArg (fun x => (e19SubsetSum x)⁻¹) (subsetCode19FourDecode_left s)).symm
        _ = ∑ m : Fin 16, (e19SubsetSum (subsetDecode19Four m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode19Four (0 : Fin 16) = ∅ by decide, e19SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 15, (e19SubsetSum (subsetDecode19Four i.succ))⁻¹) =
            ∑ i : Fin 15, e19InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact e19DecodeInvSucc i
        _ = 0 := e19InvFor_sum_zero

theorem e19Subspace_isZeroSum_probe : Carlet.IsZeroSum e19Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset e19Subspace).erase 0, x⁻¹) = 0
  rw [e19Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
      (f := fun s => (e19SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 4))) (by simp)
  rw [e19SubsetSum_empty, inv_zero, add_zero, e19SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_524288_four_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f19) 4 :=
  ⟨e19Subspace, e19Subspace_finrank, e19Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n19_four_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 19) : Carlet.HasZeroSumSubspace K 4 := by
  have hsrc : Fintype.card (AdjoinRoot f19) = Fintype.card K := by
    rw [adjoinRoot19_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 4 hsrc hasZeroSumSubspace_524288_four_probe

#print axioms e19SubsetSum_all_inverse_zero
#print axioms hasZeroSumSubspace_n19_four_card_probe
