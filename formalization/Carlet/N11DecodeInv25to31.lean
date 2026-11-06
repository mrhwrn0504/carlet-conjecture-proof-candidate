import Carlet.N11DecodeInv17to24
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

theorem certDecodeInv25 : (certSubsetSum (subsetDecode (⟨25, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI25 := by
  have hc : subsetCode ({0,3,4} : Finset (Fin 5)) = (⟨25, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum25]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin25).symm

theorem certDecodeInv26 : (certSubsetSum (subsetDecode (⟨26, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI26 := by
  have hc : subsetCode ({1,3,4} : Finset (Fin 5)) = (⟨26, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum26]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin26).symm

theorem certDecodeInv27 : (certSubsetSum (subsetDecode (⟨27, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI27 := by
  have hc : subsetCode ({0,1,3,4} : Finset (Fin 5)) = (⟨27, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum27]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin27).symm

theorem certDecodeInv28 : (certSubsetSum (subsetDecode (⟨28, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI28 := by
  have hc : subsetCode ({2,3,4} : Finset (Fin 5)) = (⟨28, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum28]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin28).symm

theorem certDecodeInv29 : (certSubsetSum (subsetDecode (⟨29, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI29 := by
  have hc : subsetCode ({0,2,3,4} : Finset (Fin 5)) = (⟨29, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum29]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin29).symm

theorem certDecodeInv30 : (certSubsetSum (subsetDecode (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI30 := by
  have hc : subsetCode ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum30]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin30).symm

theorem certDecodeInv31 : (certSubsetSum (subsetDecode (⟨31, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI31 := by
  have hc : subsetCode ({0,1,2,3,4} : Finset (Fin 5)) = (⟨31, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum31]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin31).symm

#print axioms certDecodeInv25
#print axioms certDecodeInv31


