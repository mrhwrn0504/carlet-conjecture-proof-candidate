import Carlet.N19FourCodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
theorem e19DecodeInv01 : (e19SubsetSum (subsetDecode19Four (⟨1, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I01 := by
  have hc : subsetCode19Four ({0} : Finset (Fin 4)) = (⟨1, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin01).symm
theorem e19DecodeInv02 : (e19SubsetSum (subsetDecode19Four (⟨2, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I02 := by
  have hc : subsetCode19Four ({1} : Finset (Fin 4)) = (⟨2, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin02).symm
theorem e19DecodeInv03 : (e19SubsetSum (subsetDecode19Four (⟨3, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I03 := by
  have hc : subsetCode19Four ({0,1} : Finset (Fin 4)) = (⟨3, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin03).symm
theorem e19DecodeInv04 : (e19SubsetSum (subsetDecode19Four (⟨4, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I04 := by
  have hc : subsetCode19Four ({2} : Finset (Fin 4)) = (⟨4, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin04).symm
theorem e19DecodeInv05 : (e19SubsetSum (subsetDecode19Four (⟨5, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I05 := by
  have hc : subsetCode19Four ({0,2} : Finset (Fin 4)) = (⟨5, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin05).symm
theorem e19DecodeInv06 : (e19SubsetSum (subsetDecode19Four (⟨6, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I06 := by
  have hc : subsetCode19Four ({1,2} : Finset (Fin 4)) = (⟨6, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin06).symm
theorem e19DecodeInv07 : (e19SubsetSum (subsetDecode19Four (⟨7, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I07 := by
  have hc : subsetCode19Four ({0,1,2} : Finset (Fin 4)) = (⟨7, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin07).symm
theorem e19DecodeInv08 : (e19SubsetSum (subsetDecode19Four (⟨8, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I08 := by
  have hc : subsetCode19Four ({3} : Finset (Fin 4)) = (⟨8, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin08).symm
theorem e19DecodeInv09 : (e19SubsetSum (subsetDecode19Four (⟨9, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I09 := by
  have hc : subsetCode19Four ({0,3} : Finset (Fin 4)) = (⟨9, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin09).symm
theorem e19DecodeInv10 : (e19SubsetSum (subsetDecode19Four (⟨10, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I10 := by
  have hc : subsetCode19Four ({1,3} : Finset (Fin 4)) = (⟨10, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin10).symm
theorem e19DecodeInv11 : (e19SubsetSum (subsetDecode19Four (⟨11, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I11 := by
  have hc : subsetCode19Four ({0,1,3} : Finset (Fin 4)) = (⟨11, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin19).symm
theorem e19DecodeInv12 : (e19SubsetSum (subsetDecode19Four (⟨12, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I12 := by
  have hc : subsetCode19Four ({2,3} : Finset (Fin 4)) = (⟨12, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin12).symm
theorem e19DecodeInv13 : (e19SubsetSum (subsetDecode19Four (⟨13, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I13 := by
  have hc : subsetCode19Four ({0,2,3} : Finset (Fin 4)) = (⟨13, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin13).symm
theorem e19DecodeInv14 : (e19SubsetSum (subsetDecode19Four (⟨14, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I14 := by
  have hc : subsetCode19Four ({1,2,3} : Finset (Fin 4)) = (⟨14, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin14).symm
theorem e19DecodeInv15 : (e19SubsetSum (subsetDecode19Four (⟨15, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f19 e19I15 := by
  have hc : subsetCode19Four ({0,1,2,3} : Finset (Fin 4)) = (⟨15, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode19Four, subsetCodeNat19Four, Finset.sum_singleton]
  rw [← hc, subsetCode19FourDecode_left]
  simp only [e19SubsetSum]
  rw [e19SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right e19InvAdjoin15).symm

#print axioms e19DecodeInv01
#print axioms e19DecodeInv15
