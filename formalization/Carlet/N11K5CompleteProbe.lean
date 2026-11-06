import Carlet.N11InvForTerm
import Carlet.N11FieldBridgeProbe
import Carlet.FieldTransport
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

theorem certSubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 5), (certSubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 5))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 5), (certSubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (certSubsetSum s)⁻¹ := by
      rw [← hp]
    _ = ∑ m : Fin 32, (certSubsetSum (subsetDecode m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (certSubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 32)), (certSubsetSum (subsetDecode m))⁻¹ := by
          apply Finset.sum_equiv subsetCodeEquiv
          · intro s
            simp
          · intro s hs
            simpa [subsetCodeEquiv] using
              (congrArg (fun x => (certSubsetSum x)⁻¹) (subsetCodeDecode_left s)).symm
        _ = ∑ m : Fin 32, (certSubsetSum (subsetDecode m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode (0 : Fin 32) = ∅ by decide, certSubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 31, (certSubsetSum (subsetDecode i.succ))⁻¹) =
            ∑ i : Fin 31, certInvFor i := by
          apply Fintype.sum_congr
          intro i
          exact certDecodeInvSucc i
        _ = 0 := certInvFor_sum_zero

theorem certSubspace_isZeroSum_probe : Carlet.IsZeroSum certSubspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset certSubspace).erase 0, x⁻¹) = 0
  rw [certSubspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 5))))
      (f := fun s => (certSubsetSum s)⁻¹) (a := (∅ : Finset (Fin 5))) (by simp)
  rw [certSubsetSum_empty, inv_zero, add_zero, certSubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_2048_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f) 5 :=
  ⟨certSubspace, certSubspace_finrank, certSubspace_isZeroSum_probe⟩

theorem hasZeroSumSubspace_n11_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 11) : Carlet.HasZeroSumSubspace K 5 := by
  have hsrc : Fintype.card (AdjoinRoot f) = Fintype.card K := by
    rw [adjoinRoot11_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 5 hsrc hasZeroSumSubspace_2048_probe

#print axioms certSubsetSum_all_inverse_zero
#print axioms certSubspace_isZeroSum_probe
#print axioms hasZeroSumSubspace_2048_probe
#print axioms hasZeroSumSubspace_n11_card_probe



