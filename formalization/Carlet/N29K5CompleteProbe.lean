import Carlet.N29K5SupportLinearProbe
import Carlet.N29K5InvForTermProbe
import Carlet.N29K5FieldBridgeProbe
import Carlet.FieldTransport
import Mathlib.Tactic
open Carlet
set_option linter.unnecessarySeqFocus false
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩

theorem n29K5SubsetSum_all_inverse_zero :
    (∑ s : Finset (Fin 5), (n29K5SubsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 5))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 5), (n29K5SubsetSum s)⁻¹) =
        ∑ s ∈ Finset.univ.powerset, (n29K5SubsetSum s)⁻¹ := by
      rw [← hp]
    _ = ∑ m : Fin 32, (n29K5SubsetSum (n29K5SubsetDecode m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (n29K5SubsetSum s)⁻¹) =
            ∑ m ∈ (Finset.univ : Finset (Fin 32)), (n29K5SubsetSum (n29K5SubsetDecode m))⁻¹ := by
          apply Finset.sum_equiv n29K5SubsetCodeEquiv
          · intro s
            simp
          · intro s hs
            simpa [n29K5SubsetCodeEquiv] using
              (congrArg (fun x => (n29K5SubsetSum x)⁻¹) (n29K5SubsetCodeDecode_left s)).symm
        _ = ∑ m : Fin 32, (n29K5SubsetSum (n29K5SubsetDecode m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show n29K5SubsetDecode (0 : Fin 32) = ∅ by decide, n29K5SubsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 31, (n29K5SubsetSum (n29K5SubsetDecode i.succ))⁻¹) =
            ∑ i : Fin 31, n29K5InvFor i := by
          apply Fintype.sum_congr
          intro i
          exact n29K5DecodeInvSucc i
        _ = 0 := n29K5InvFor_sum_zero

theorem n29K5Subspace_isZeroSum : Carlet.IsZeroSum n29K5Subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset n29K5Subspace).erase 0, x⁻¹) = 0
  rw [n29K5Subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 5))))
      (f := fun s => (n29K5SubsetSum s)⁻¹) (a := (∅ : Finset (Fin 5))) (by simp)
  rw [n29K5SubsetSum_empty, inv_zero, add_zero, n29K5SubsetSum_all_inverse_zero] at h
  exact h

theorem hasZeroSumSubspace_2pow29_five_probe : Carlet.HasZeroSumSubspace (AdjoinRoot f29K5) 5 :=
  ⟨n29K5Subspace, n29K5Subspace_finrank, n29K5Subspace_isZeroSum⟩

theorem hasZeroSumSubspace_n29_card_probe {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 29) : Carlet.HasZeroSumSubspace K 5 := by
  have hsrc : Fintype.card (AdjoinRoot f29K5) = Fintype.card K := by
    rw [adjoinRoot29K5_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 5 hsrc hasZeroSumSubspace_2pow29_five_probe

#print axioms n29K5SubsetSum_all_inverse_zero
#print axioms n29K5Subspace_isZeroSum
#print axioms hasZeroSumSubspace_2pow29_five_probe
#print axioms hasZeroSumSubspace_n29_card_probe







