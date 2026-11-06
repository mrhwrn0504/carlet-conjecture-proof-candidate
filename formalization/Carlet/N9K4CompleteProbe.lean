import Carlet.N9InvForTerm
import Carlet.FieldTransport
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩

theorem d9SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 4), (d9SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 4))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 4), (d9SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (d9SubsetSum s)⁻¹ := by rw [← hp]
    _ = ∑ m : Fin 16, (d9SubsetSum (subsetDecode9 m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (d9SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 16)), (d9SubsetSum (subsetDecode9 m))⁻¹ := by
          apply Finset.sum_equiv subsetCode9Equiv
          · intro s; simp
          · intro s hs
            simpa [subsetCode9Equiv] using
              (congrArg (fun x => (d9SubsetSum x)⁻¹) (subsetCode9Decode_left s)).symm
        _ = ∑ m : Fin 16, (d9SubsetSum (subsetDecode9 m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode9 (0 : Fin 16) = ∅ by decide, d9SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 15, (d9SubsetSum (subsetDecode9 i.succ))⁻¹) =
            ∑ i : Fin 15, d9InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact d9DecodeInvSucc i
        _ = 0 := d9InvFor_sum_zero

theorem d9Subspace_isZeroSum_probe : Carlet.IsZeroSum d9Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset d9Subspace).erase 0, x⁻¹) = 0
  rw [d9Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
      (f := fun s => (d9SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 4))) (by simp)
  rw [d9SubsetSum_empty, inv_zero, add_zero, d9SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_512_four_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f9) 4 :=
  ⟨d9Subspace, d9Subspace_finrank, d9Subspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n9_four_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 9) : Carlet.HasZeroSumSubspace K 4 := by
  have hsrc : Fintype.card (AdjoinRoot f9) = Fintype.card K := by
    rw [adjoinRoot9_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 4 hsrc hasZeroSumSubspace_512_four_probe

#print axioms d9SubsetSum_all_inverse_zero
#print axioms hasZeroSumSubspace_n9_four_card_probe
