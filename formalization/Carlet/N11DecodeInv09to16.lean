import Carlet.N11DecodeInv02to08
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

theorem certDecodeInv09 : (certSubsetSum (subsetDecode (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI09 := by
  have hc : subsetCode ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum09]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin09).symm

theorem certDecodeInv10 : (certSubsetSum (subsetDecode (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI10 := by
  have hc : subsetCode ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum10]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin10).symm

theorem certDecodeInv11 : (certSubsetSum (subsetDecode (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI11 := by
  have hc : subsetCode ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum11]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin11).symm

theorem certDecodeInv12 : (certSubsetSum (subsetDecode (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI12 := by
  have hc : subsetCode ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum12]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin12).symm

theorem certDecodeInv13 : (certSubsetSum (subsetDecode (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI13 := by
  have hc : subsetCode ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum13]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin13).symm

theorem certDecodeInv14 : (certSubsetSum (subsetDecode (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI14 := by
  have hc : subsetCode ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum14]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin14).symm

theorem certDecodeInv15 : (certSubsetSum (subsetDecode (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI15 := by
  have hc : subsetCode ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum15]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin15).symm

theorem certDecodeInv16 : (certSubsetSum (subsetDecode (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI16 := by
  have hc : subsetCode ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum16]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin16).symm

#print axioms certDecodeInv09
#print axioms certDecodeInv16


