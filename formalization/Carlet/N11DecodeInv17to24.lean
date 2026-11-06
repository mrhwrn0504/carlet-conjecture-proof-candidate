import Carlet.N11DecodeInv09to16
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

theorem certDecodeInv17 : (certSubsetSum (subsetDecode (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI17 := by
  have hc : subsetCode ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum17]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin17).symm

theorem certDecodeInv18 : (certSubsetSum (subsetDecode (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI18 := by
  have hc : subsetCode ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum18]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin18).symm

theorem certDecodeInv19 : (certSubsetSum (subsetDecode (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI19 := by
  have hc : subsetCode ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum19]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin19).symm

theorem certDecodeInv20 : (certSubsetSum (subsetDecode (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI20 := by
  have hc : subsetCode ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum20]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin20).symm

theorem certDecodeInv21 : (certSubsetSum (subsetDecode (⟨21, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI21 := by
  have hc : subsetCode ({0,2,4} : Finset (Fin 5)) = (⟨21, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum21]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin21).symm

theorem certDecodeInv22 : (certSubsetSum (subsetDecode (⟨22, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI22 := by
  have hc : subsetCode ({1,2,4} : Finset (Fin 5)) = (⟨22, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum22]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin22).symm

theorem certDecodeInv23 : (certSubsetSum (subsetDecode (⟨23, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI23 := by
  have hc : subsetCode ({0,1,2,4} : Finset (Fin 5)) = (⟨23, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum23]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin23).symm

theorem certDecodeInv24 : (certSubsetSum (subsetDecode (⟨24, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI24 := by
  have hc : subsetCode ({3,4} : Finset (Fin 5)) = (⟨24, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum24]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin24).symm

#print axioms certDecodeInv17
#print axioms certDecodeInv24


