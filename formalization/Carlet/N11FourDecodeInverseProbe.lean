import Carlet.N11FourCodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
theorem e11DecodeInv01 : (e11SubsetSum (subsetDecode11Four (⟨1, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I01 := by
  have hc : subsetCode11Four ({0} : Finset (Fin 4)) = (⟨1, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin01).symm
theorem e11DecodeInv02 : (e11SubsetSum (subsetDecode11Four (⟨2, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I02 := by
  have hc : subsetCode11Four ({1} : Finset (Fin 4)) = (⟨2, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin02).symm
theorem e11DecodeInv03 : (e11SubsetSum (subsetDecode11Four (⟨3, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I03 := by
  have hc : subsetCode11Four ({0,1} : Finset (Fin 4)) = (⟨3, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin03).symm
theorem e11DecodeInv04 : (e11SubsetSum (subsetDecode11Four (⟨4, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I04 := by
  have hc : subsetCode11Four ({2} : Finset (Fin 4)) = (⟨4, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin04).symm
theorem e11DecodeInv05 : (e11SubsetSum (subsetDecode11Four (⟨5, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I05 := by
  have hc : subsetCode11Four ({0,2} : Finset (Fin 4)) = (⟨5, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin05).symm
theorem e11DecodeInv06 : (e11SubsetSum (subsetDecode11Four (⟨6, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I06 := by
  have hc : subsetCode11Four ({1,2} : Finset (Fin 4)) = (⟨6, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin06).symm
theorem e11DecodeInv07 : (e11SubsetSum (subsetDecode11Four (⟨7, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I07 := by
  have hc : subsetCode11Four ({0,1,2} : Finset (Fin 4)) = (⟨7, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin07).symm
theorem e11DecodeInv08 : (e11SubsetSum (subsetDecode11Four (⟨8, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I08 := by
  have hc : subsetCode11Four ({3} : Finset (Fin 4)) = (⟨8, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin08).symm
theorem e11DecodeInv09 : (e11SubsetSum (subsetDecode11Four (⟨9, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I09 := by
  have hc : subsetCode11Four ({0,3} : Finset (Fin 4)) = (⟨9, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin09).symm
theorem e11DecodeInv10 : (e11SubsetSum (subsetDecode11Four (⟨10, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I10 := by
  have hc : subsetCode11Four ({1,3} : Finset (Fin 4)) = (⟨10, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin10).symm
theorem e11DecodeInv11 : (e11SubsetSum (subsetDecode11Four (⟨11, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I11 := by
  have hc : subsetCode11Four ({0,1,3} : Finset (Fin 4)) = (⟨11, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin11).symm
theorem e11DecodeInv12 : (e11SubsetSum (subsetDecode11Four (⟨12, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I12 := by
  have hc : subsetCode11Four ({2,3} : Finset (Fin 4)) = (⟨12, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin12).symm
theorem e11DecodeInv13 : (e11SubsetSum (subsetDecode11Four (⟨13, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I13 := by
  have hc : subsetCode11Four ({0,2,3} : Finset (Fin 4)) = (⟨13, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin13).symm
theorem e11DecodeInv14 : (e11SubsetSum (subsetDecode11Four (⟨14, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I14 := by
  have hc : subsetCode11Four ({1,2,3} : Finset (Fin 4)) = (⟨14, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin14).symm
theorem e11DecodeInv15 : (e11SubsetSum (subsetDecode11Four (⟨15, by omega⟩ : Fin 16)))⁻¹ = AdjoinRoot.mk f e11I15 := by
  have hc : subsetCode11Four ({0,1,2,3} : Finset (Fin 4)) = (⟨15, by omega⟩ : Fin 16) := by
    apply Fin.ext
    simp [subsetCode11Four, subsetCodeNat11Four, Finset.sum_singleton]
  rw [← hc, subsetCode11FourDecode_left]
  simp only [e11SubsetSum]
  rw [e11SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right e11InvAdjoin15).symm

#print axioms e11DecodeInv01
#print axioms e11DecodeInv15
