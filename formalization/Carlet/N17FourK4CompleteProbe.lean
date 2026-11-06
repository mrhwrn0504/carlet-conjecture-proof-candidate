import Carlet.N17FourInvForTerm
import Carlet.FieldTransport
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩

theorem e17SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 4), (e17SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 4))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 4), (e17SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (e17SubsetSum s)⁻¹ := by rw [← hp]
    _ = ∑ m : Fin 16, (e17SubsetSum (subsetDecode17Four m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (e17SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 16)), (e17SubsetSum (subsetDecode17Four m))⁻¹ := by
          apply Finset.sum_equiv subsetCode17FourEquiv
          · intro s; simp
          · intro s hs
            simpa [subsetCode17FourEquiv] using
              (congrArg (fun x => (e17SubsetSum x)⁻¹) (subsetCode17FourDecode_left s)).symm
        _ = ∑ m : Fin 16, (e17SubsetSum (subsetDecode17Four m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode17Four (0 : Fin 16) = ∅ by decide, e17SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 15, (e17SubsetSum (subsetDecode17Four i.succ))⁻¹) =
            ∑ i : Fin 15, e17InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact e17DecodeInvSucc i
        _ = 0 := e17InvFor_sum_zero

theorem e17Subspace_isZeroSum_probe : Carlet.IsZeroSum e17Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset e17Subspace).erase 0, x⁻¹) = 0
  rw [e17Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
      (f := fun s => (e17SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 4))) (by simp)
  rw [e17SubsetSum_empty, inv_zero, add_zero, e17SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_131072_four_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f17) 4 :=
  ⟨e17Subspace, e17Subspace_finrank, e17Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n17_four_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 17) : Carlet.HasZeroSumSubspace K 4 := by
  have hsrc : Fintype.card (AdjoinRoot f17) = Fintype.card K := by
    rw [adjoinRoot17_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 4 hsrc hasZeroSumSubspace_131072_four_probe

#print axioms e17SubsetSum_all_inverse_zero
#print axioms hasZeroSumSubspace_n17_four_card_probe
