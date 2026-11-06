import Carlet.N11DecodeInv01Fast
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

theorem certDecodeInv02 : (certSubsetSum (subsetDecode (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI02 := by
  have hc : subsetCode ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum02]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin02).symm

theorem certDecodeInv03 : (certSubsetSum (subsetDecode (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI03 := by
  have hc : subsetCode ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum03]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin03).symm

theorem certDecodeInv04 : (certSubsetSum (subsetDecode (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI04 := by
  have hc : subsetCode ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum04]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin04).symm

theorem certDecodeInv05 : (certSubsetSum (subsetDecode (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI05 := by
  have hc : subsetCode ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum05]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin05).symm

theorem certDecodeInv06 : (certSubsetSum (subsetDecode (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI06 := by
  have hc : subsetCode ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum06]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin06).symm

theorem certDecodeInv07 : (certSubsetSum (subsetDecode (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI07 := by
  have hc : subsetCode ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum07]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin07).symm

theorem certDecodeInv08 : (certSubsetSum (subsetDecode (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f certI08 := by
  have hc : subsetCode ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode, subsetCodeNat, Finset.sum_singleton]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum08]
  exact (eq_inv_of_mul_eq_one_right certInvAdjoin08).symm

#print axioms certDecodeInv02
#print axioms certDecodeInv08


