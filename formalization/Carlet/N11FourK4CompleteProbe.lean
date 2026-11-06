import Carlet.N11FourInvForTerm
import Carlet.FieldTransport
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

theorem e11SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 4), (e11SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 4))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 4), (e11SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (e11SubsetSum s)⁻¹ := by rw [← hp]
    _ = ∑ m : Fin 16, (e11SubsetSum (subsetDecode11Four m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (e11SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 16)), (e11SubsetSum (subsetDecode11Four m))⁻¹ := by
          apply Finset.sum_equiv subsetCode11FourEquiv
          · intro s; simp
          · intro s hs
            simpa [subsetCode11FourEquiv] using
              (congrArg (fun x => (e11SubsetSum x)⁻¹) (subsetCode11FourDecode_left s)).symm
        _ = ∑ m : Fin 16, (e11SubsetSum (subsetDecode11Four m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode11Four (0 : Fin 16) = ∅ by decide, e11SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 15, (e11SubsetSum (subsetDecode11Four i.succ))⁻¹) =
            ∑ i : Fin 15, e11InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact e11DecodeInvSucc i
        _ = 0 := e11InvFor_sum_zero

theorem e11Subspace_isZeroSum_probe : Carlet.IsZeroSum e11Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset e11Subspace).erase 0, x⁻¹) = 0
  rw [e11Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
      (f := fun s => (e11SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 4))) (by simp)
  rw [e11SubsetSum_empty, inv_zero, add_zero, e11SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_2048_four_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f) 4 :=
  ⟨e11Subspace, e11Subspace_finrank, e11Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n11_four_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 11) : Carlet.HasZeroSumSubspace K 4 := by
  have hsrc : Fintype.card (AdjoinRoot f) = Fintype.card K := by
    rw [adjoinRoot11_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 4 hsrc hasZeroSumSubspace_2048_four_probe

#print axioms e11SubsetSum_all_inverse_zero
#print axioms hasZeroSumSubspace_n11_four_card_probe
