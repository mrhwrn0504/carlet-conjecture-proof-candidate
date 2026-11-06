import Carlet.N17FourCodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
theorem e17DecodeInv01 : (e17SubsetSum (subsetDecode17Four (⟨1, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I01 := by
  have hc : subsetCode17Four ({0} : Finset (Fin 4)) = (⟨1, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin01).symm
theorem e17DecodeInv02 : (e17SubsetSum (subsetDecode17Four (⟨2, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I02 := by
  have hc : subsetCode17Four ({1} : Finset (Fin 4)) = (⟨2, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin02).symm
theorem e17DecodeInv03 : (e17SubsetSum (subsetDecode17Four (⟨3, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I03 := by
  have hc : subsetCode17Four ({0,1} : Finset (Fin 4)) = (⟨3, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin03).symm
theorem e17DecodeInv04 : (e17SubsetSum (subsetDecode17Four (⟨4, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I04 := by
  have hc : subsetCode17Four ({2} : Finset (Fin 4)) = (⟨4, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin04).symm
theorem e17DecodeInv05 : (e17SubsetSum (subsetDecode17Four (⟨5, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I05 := by
  have hc : subsetCode17Four ({0,2} : Finset (Fin 4)) = (⟨5, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin05).symm
theorem e17DecodeInv06 : (e17SubsetSum (subsetDecode17Four (⟨6, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I06 := by
  have hc : subsetCode17Four ({1,2} : Finset (Fin 4)) = (⟨6, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin06).symm
theorem e17DecodeInv07 : (e17SubsetSum (subsetDecode17Four (⟨7, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I07 := by
  have hc : subsetCode17Four ({0,1,2} : Finset (Fin 4)) = (⟨7, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin07).symm
theorem e17DecodeInv08 : (e17SubsetSum (subsetDecode17Four (⟨8, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I08 := by
  have hc : subsetCode17Four ({3} : Finset (Fin 4)) = (⟨8, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin08).symm
theorem e17DecodeInv09 : (e17SubsetSum (subsetDecode17Four (⟨9, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I09 := by
  have hc : subsetCode17Four ({0,3} : Finset (Fin 4)) = (⟨9, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin09).symm
theorem e17DecodeInv10 : (e17SubsetSum (subsetDecode17Four (⟨10, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I10 := by
  have hc : subsetCode17Four ({1,3} : Finset (Fin 4)) = (⟨10, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin10).symm
theorem e17DecodeInv11 : (e17SubsetSum (subsetDecode17Four (⟨11, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I11 := by
  have hc : subsetCode17Four ({0,1,3} : Finset (Fin 4)) = (⟨11, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin17).symm
theorem e17DecodeInv12 : (e17SubsetSum (subsetDecode17Four (⟨12, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I12 := by
  have hc : subsetCode17Four ({2,3} : Finset (Fin 4)) = (⟨12, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin12).symm
theorem e17DecodeInv13 : (e17SubsetSum (subsetDecode17Four (⟨13, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I13 := by
  have hc : subsetCode17Four ({0,2,3} : Finset (Fin 4)) = (⟨13, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin13).symm
theorem e17DecodeInv14 : (e17SubsetSum (subsetDecode17Four (⟨14, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I14 := by
  have hc : subsetCode17Four ({1,2,3} : Finset (Fin 4)) = (⟨14, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin14).symm
theorem e17DecodeInv15 : (e17SubsetSum (subsetDecode17Four (⟨15, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f17 e17I15 := by
  have hc : subsetCode17Four ({0,1,2,3} : Finset (Fin 4)) = (⟨15, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode17Four, subsetCodeNat17Four, Finset.sum_singleton]
  rw [← hc, subsetCode17FourDecode_left]
  simp only [e17SubsetSum]
  rw [e17SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right e17InvAdjoin15).symm

#print axioms e17DecodeInv01
#print axioms e17DecodeInv15
