import Carlet.N9CodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
theorem d9DecodeInv01 : (d9SubsetSum (subsetDecode9 (⟨1, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I01 := by
  have hc : subsetCode9 ({0} : Finset (Fin 4)) = (⟨1, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin01).symm
theorem d9DecodeInv02 : (d9SubsetSum (subsetDecode9 (⟨2, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I02 := by
  have hc : subsetCode9 ({1} : Finset (Fin 4)) = (⟨2, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin02).symm
theorem d9DecodeInv03 : (d9SubsetSum (subsetDecode9 (⟨3, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I03 := by
  have hc : subsetCode9 ({0,1} : Finset (Fin 4)) = (⟨3, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin03).symm
theorem d9DecodeInv04 : (d9SubsetSum (subsetDecode9 (⟨4, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I04 := by
  have hc : subsetCode9 ({2} : Finset (Fin 4)) = (⟨4, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin04).symm
theorem d9DecodeInv05 : (d9SubsetSum (subsetDecode9 (⟨5, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I05 := by
  have hc : subsetCode9 ({0,2} : Finset (Fin 4)) = (⟨5, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin05).symm
theorem d9DecodeInv06 : (d9SubsetSum (subsetDecode9 (⟨6, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I06 := by
  have hc : subsetCode9 ({1,2} : Finset (Fin 4)) = (⟨6, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin06).symm
theorem d9DecodeInv07 : (d9SubsetSum (subsetDecode9 (⟨7, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I07 := by
  have hc : subsetCode9 ({0,1,2} : Finset (Fin 4)) = (⟨7, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin07).symm
theorem d9DecodeInv08 : (d9SubsetSum (subsetDecode9 (⟨8, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I08 := by
  have hc : subsetCode9 ({3} : Finset (Fin 4)) = (⟨8, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin08).symm
theorem d9DecodeInv09 : (d9SubsetSum (subsetDecode9 (⟨9, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I09 := by
  have hc : subsetCode9 ({0,3} : Finset (Fin 4)) = (⟨9, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin09).symm
theorem d9DecodeInv10 : (d9SubsetSum (subsetDecode9 (⟨10, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I10 := by
  have hc : subsetCode9 ({1,3} : Finset (Fin 4)) = (⟨10, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin10).symm
theorem d9DecodeInv11 : (d9SubsetSum (subsetDecode9 (⟨11, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I11 := by
  have hc : subsetCode9 ({0,1,3} : Finset (Fin 4)) = (⟨11, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin11).symm
theorem d9DecodeInv12 : (d9SubsetSum (subsetDecode9 (⟨12, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I12 := by
  have hc : subsetCode9 ({2,3} : Finset (Fin 4)) = (⟨12, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin12).symm
theorem d9DecodeInv13 : (d9SubsetSum (subsetDecode9 (⟨13, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I13 := by
  have hc : subsetCode9 ({0,2,3} : Finset (Fin 4)) = (⟨13, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin13).symm
theorem d9DecodeInv14 : (d9SubsetSum (subsetDecode9 (⟨14, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I14 := by
  have hc : subsetCode9 ({1,2,3} : Finset (Fin 4)) = (⟨14, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin14).symm
theorem d9DecodeInv15 : (d9SubsetSum (subsetDecode9 (⟨15, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f9 d9I15 := by
  have hc : subsetCode9 ({0,1,2,3} : Finset (Fin 4)) = (⟨15, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode9, subsetCodeNat9, Finset.sum_singleton]
  rw [← hc, subsetCode9Decode_left]
  simp only [d9SubsetSum]
  rw [d9SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right d9InvAdjoin15).symm

#print axioms d9DecodeInv01
#print axioms d9DecodeInv15
