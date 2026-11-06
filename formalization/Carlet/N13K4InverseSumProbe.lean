import Carlet.N13K4CompleteProbe
import Carlet.FieldTransport
import Mathlib.Tactic
open Polynomial Carlet
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
namespace N13K4
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
def inverseFor (i : Fin 15) : AdjoinRoot f13 := match i.val with
| 0 => AdjoinRoot.mk f13 Carlet.n13K4I01
| 1 => AdjoinRoot.mk f13 Carlet.n13K4I02
| 2 => AdjoinRoot.mk f13 Carlet.n13K4I03
| 3 => AdjoinRoot.mk f13 Carlet.n13K4I04
| 4 => AdjoinRoot.mk f13 Carlet.n13K4I05
| 5 => AdjoinRoot.mk f13 Carlet.n13K4I06
| 6 => AdjoinRoot.mk f13 Carlet.n13K4I07
| 7 => AdjoinRoot.mk f13 Carlet.n13K4I08
| 8 => AdjoinRoot.mk f13 Carlet.n13K4I09
| 9 => AdjoinRoot.mk f13 Carlet.n13K4I10
| 10 => AdjoinRoot.mk f13 Carlet.n13K4I11
| 11 => AdjoinRoot.mk f13 Carlet.n13K4I12
| 12 => AdjoinRoot.mk f13 Carlet.n13K4I13
| 13 => AdjoinRoot.mk f13 Carlet.n13K4I14
| 14 => AdjoinRoot.mk f13 Carlet.n13K4I15
| _ => 0

theorem decodeInverseSucc (i : Fin 15) : (subsetSum (subsetDecode (Fin.succ i)))⁻¹ = inverseFor i := by
  classical
  fin_cases i
  case «0» =>
    have hc : subsetCode ({0} : Finset (Fin 4)) = (Fin.succ (⟨0, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum01]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin01).symm
  case «1» =>
    have hc : subsetCode ({1} : Finset (Fin 4)) = (Fin.succ (⟨1, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum02]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin02).symm
  case «2» =>
    have hc : subsetCode ({0,1} : Finset (Fin 4)) = (Fin.succ (⟨2, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum03]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin03).symm
  case «3» =>
    have hc : subsetCode ({2} : Finset (Fin 4)) = (Fin.succ (⟨3, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum04]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin04).symm
  case «4» =>
    have hc : subsetCode ({0,2} : Finset (Fin 4)) = (Fin.succ (⟨4, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum05]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin05).symm
  case «5» =>
    have hc : subsetCode ({1,2} : Finset (Fin 4)) = (Fin.succ (⟨5, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum06]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin06).symm
  case «6» =>
    have hc : subsetCode ({0,1,2} : Finset (Fin 4)) = (Fin.succ (⟨6, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum07]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin07).symm
  case «7» =>
    have hc : subsetCode ({3} : Finset (Fin 4)) = (Fin.succ (⟨7, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum08]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin08).symm
  case «8» =>
    have hc : subsetCode ({0,3} : Finset (Fin 4)) = (Fin.succ (⟨8, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum09]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin09).symm
  case «9» =>
    have hc : subsetCode ({1,3} : Finset (Fin 4)) = (Fin.succ (⟨9, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum10]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin10).symm
  case «10» =>
    have hc : subsetCode ({0,1,3} : Finset (Fin 4)) = (Fin.succ (⟨10, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum11]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin11).symm
  case «11» =>
    have hc : subsetCode ({2,3} : Finset (Fin 4)) = (Fin.succ (⟨11, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum12]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin12).symm
  case «12» =>
    have hc : subsetCode ({0,2,3} : Finset (Fin 4)) = (Fin.succ (⟨12, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum13]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin13).symm
  case «13» =>
    have hc : subsetCode ({1,2,3} : Finset (Fin 4)) = (Fin.succ (⟨13, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum14]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin14).symm
  case «14» =>
    have hc : subsetCode ({0,1,2,3} : Finset (Fin 4)) = (Fin.succ (⟨14, by omega⟩ : Fin 15)) := by
      apply Fin.ext
      simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
    rw [← hc, subsetCodeDecode_left]
    simp only [subsetSum]
    rw [subsetSum15]
    exact (eq_inv_of_mul_eq_one_right Carlet.n13K4InvAdjoin15).symm
#print axioms decodeInverseSucc

theorem inverseFor_sum_as_list : (∑ i : Fin 15, inverseFor i) = AdjoinRoot.mk f13 Carlet.n13K4I01 + AdjoinRoot.mk f13 Carlet.n13K4I02 + AdjoinRoot.mk f13 Carlet.n13K4I03 + AdjoinRoot.mk f13 Carlet.n13K4I04 + AdjoinRoot.mk f13 Carlet.n13K4I05 + AdjoinRoot.mk f13 Carlet.n13K4I06 + AdjoinRoot.mk f13 Carlet.n13K4I07 + AdjoinRoot.mk f13 Carlet.n13K4I08 + AdjoinRoot.mk f13 Carlet.n13K4I09 + AdjoinRoot.mk f13 Carlet.n13K4I10 + AdjoinRoot.mk f13 Carlet.n13K4I11 + AdjoinRoot.mk f13 Carlet.n13K4I12 + AdjoinRoot.mk f13 Carlet.n13K4I13 + AdjoinRoot.mk f13 Carlet.n13K4I14 + AdjoinRoot.mk f13 Carlet.n13K4I15 := by
  classical
  simp only [Fin.sum_univ_succ, inverseFor]
  abel

theorem inverseFor_sum_zero : (∑ i : Fin 15, inverseFor i) = 0 := by
  rw [inverseFor_sum_as_list]
  exact Carlet.n13K4InverseSumAdjoin

theorem subsetSum_all_inverse_zero : (∑ s : Finset (Fin 4), (subsetSum s)⁻¹) = 0 := by
  classical
  have hp : (Finset.univ : Finset (Finset (Fin 4))) = Finset.univ.powerset := by
    ext s
    simp
  calc
    (∑ s : Finset (Fin 4), (subsetSum s)⁻¹) = ∑ s ∈ Finset.univ.powerset, (subsetSum s)⁻¹ := by rw [← hp]
    _ = ∑ m : Fin 16, (subsetSum (subsetDecode m))⁻¹ := by
      calc
        (∑ s ∈ Finset.univ.powerset, (subsetSum s)⁻¹) = ∑ m ∈ (Finset.univ : Finset (Fin 16)), (subsetSum (subsetDecode m))⁻¹ := by
          apply Finset.sum_equiv subsetCodeEquiv
          · intro s
            simp
          · intro s hs
            simpa [subsetCodeEquiv] using (congrArg (fun x => (subsetSum x)⁻¹) (subsetCodeDecode_left s)).symm
        _ = ∑ m : Fin 16, (subsetSum (subsetDecode m))⁻¹ := by simp
    _ = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [show subsetDecode (0 : Fin 16) = ∅ by decide, subsetSum_empty, inv_zero, zero_add]
      calc
        (∑ i : Fin 15, (subsetSum (subsetDecode i.succ))⁻¹) = ∑ i : Fin 15, inverseFor i := by
          apply Fintype.sum_congr
          intro i
          exact decodeInverseSucc i
        _ = 0 := inverseFor_sum_zero
theorem subspace_isZeroSum : Carlet.IsZeroSum subspace := by
  classical
  change (∑ x ∈ (Carlet.underlyingFinset subspace).erase 0, x⁻¹) = 0
  rw [subspace_inverse_sum_eq_subset_sum]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin 4))))
    (f := fun s => (subsetSum s)⁻¹) (a := (∅ : Finset (Fin 4))) (by simp)
  rw [subsetSum_empty, inv_zero, add_zero, subsetSum_all_inverse_zero] at h
  exact h
theorem hasZeroSumSubspace_adjoinRoot : Carlet.HasZeroSumSubspace (AdjoinRoot f13) 4 :=
  ⟨subspace, subspace_finrank, subspace_isZeroSum⟩
theorem hasZeroSumSubspace_n13_card {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (hcard : Fintype.card K = 2 ^ 13) : Carlet.HasZeroSumSubspace K 4 := by
  have hsrc : Fintype.card (AdjoinRoot f13) = Fintype.card K := by
    rw [adjoinRoot13_card, hcard]
  exact Carlet.hasZeroSumSubspace_of_card_eq 4 hsrc hasZeroSumSubspace_adjoinRoot
#print axioms subsetSum_all_inverse_zero
#print axioms subspace_isZeroSum
#print axioms hasZeroSumSubspace_n13_card
end N13K4
