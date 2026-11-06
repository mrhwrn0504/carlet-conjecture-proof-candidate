import Carlet.N19CodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
theorem c19DecodeInv01 : (c19SubsetSum (subsetDecode19 (⟨1, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I01 := by
  have hc : subsetCode19 ({0} : Finset (Fin 5)) = (⟨1, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin01).symm
theorem c19DecodeInv02 : (c19SubsetSum (subsetDecode19 (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I02 := by
  have hc : subsetCode19 ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin02).symm
theorem c19DecodeInv03 : (c19SubsetSum (subsetDecode19 (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I03 := by
  have hc : subsetCode19 ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin03).symm
theorem c19DecodeInv04 : (c19SubsetSum (subsetDecode19 (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I04 := by
  have hc : subsetCode19 ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin04).symm
theorem c19DecodeInv05 : (c19SubsetSum (subsetDecode19 (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I05 := by
  have hc : subsetCode19 ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin05).symm
theorem c19DecodeInv06 : (c19SubsetSum (subsetDecode19 (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I06 := by
  have hc : subsetCode19 ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin06).symm
theorem c19DecodeInv07 : (c19SubsetSum (subsetDecode19 (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I07 := by
  have hc : subsetCode19 ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin07).symm
theorem c19DecodeInv08 : (c19SubsetSum (subsetDecode19 (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I08 := by
  have hc : subsetCode19 ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin08).symm
theorem c19DecodeInv09 : (c19SubsetSum (subsetDecode19 (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I09 := by
  have hc : subsetCode19 ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin09).symm
theorem c19DecodeInv10 : (c19SubsetSum (subsetDecode19 (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I10 := by
  have hc : subsetCode19 ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin10).symm
theorem c19DecodeInv11 : (c19SubsetSum (subsetDecode19 (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I11 := by
  have hc : subsetCode19 ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin11).symm
theorem c19DecodeInv12 : (c19SubsetSum (subsetDecode19 (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I12 := by
  have hc : subsetCode19 ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin12).symm
theorem c19DecodeInv13 : (c19SubsetSum (subsetDecode19 (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I13 := by
  have hc : subsetCode19 ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin13).symm
theorem c19DecodeInv14 : (c19SubsetSum (subsetDecode19 (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I14 := by
  have hc : subsetCode19 ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin14).symm
theorem c19DecodeInv15 : (c19SubsetSum (subsetDecode19 (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I15 := by
  have hc : subsetCode19 ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin15).symm
theorem c19DecodeInv16 : (c19SubsetSum (subsetDecode19 (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I16 := by
  have hc : subsetCode19 ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum16]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin16).symm
theorem c19DecodeInv17 : (c19SubsetSum (subsetDecode19 (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I17 := by
  have hc : subsetCode19 ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum17]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin17).symm
theorem c19DecodeInv18 : (c19SubsetSum (subsetDecode19 (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I18 := by
  have hc : subsetCode19 ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum18]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin18).symm
theorem c19DecodeInv19 : (c19SubsetSum (subsetDecode19 (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I19 := by
  have hc : subsetCode19 ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum19]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin19).symm
theorem c19DecodeInv20 : (c19SubsetSum (subsetDecode19 (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I20 := by
  have hc : subsetCode19 ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum20]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin20).symm
theorem c19DecodeInv21 : (c19SubsetSum (subsetDecode19 (⟨21, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I21 := by
  have hc : subsetCode19 ({0,2,4} : Finset (Fin 5)) = (⟨21, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum21]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin21).symm
theorem c19DecodeInv22 : (c19SubsetSum (subsetDecode19 (⟨22, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I22 := by
  have hc : subsetCode19 ({1,2,4} : Finset (Fin 5)) = (⟨22, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum22]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin22).symm
theorem c19DecodeInv23 : (c19SubsetSum (subsetDecode19 (⟨23, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I23 := by
  have hc : subsetCode19 ({0,1,2,4} : Finset (Fin 5)) = (⟨23, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum23]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin23).symm
theorem c19DecodeInv24 : (c19SubsetSum (subsetDecode19 (⟨24, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I24 := by
  have hc : subsetCode19 ({3,4} : Finset (Fin 5)) = (⟨24, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum24]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin24).symm
theorem c19DecodeInv25 : (c19SubsetSum (subsetDecode19 (⟨25, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I25 := by
  have hc : subsetCode19 ({0,3,4} : Finset (Fin 5)) = (⟨25, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum25]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin25).symm
theorem c19DecodeInv26 : (c19SubsetSum (subsetDecode19 (⟨26, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I26 := by
  have hc : subsetCode19 ({1,3,4} : Finset (Fin 5)) = (⟨26, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum26]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin26).symm
theorem c19DecodeInv27 : (c19SubsetSum (subsetDecode19 (⟨27, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I27 := by
  have hc : subsetCode19 ({0,1,3,4} : Finset (Fin 5)) = (⟨27, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum27]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin27).symm
theorem c19DecodeInv28 : (c19SubsetSum (subsetDecode19 (⟨28, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I28 := by
  have hc : subsetCode19 ({2,3,4} : Finset (Fin 5)) = (⟨28, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum28]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin28).symm
theorem c19DecodeInv29 : (c19SubsetSum (subsetDecode19 (⟨29, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I29 := by
  have hc : subsetCode19 ({0,2,3,4} : Finset (Fin 5)) = (⟨29, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum29]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin29).symm
theorem c19DecodeInv30 : (c19SubsetSum (subsetDecode19 (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I30 := by
  have hc : subsetCode19 ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum30]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin30).symm
theorem c19DecodeInv31 : (c19SubsetSum (subsetDecode19 (⟨31, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f19 c19I31 := by
  have hc : subsetCode19 ({0,1,2,3,4} : Finset (Fin 5)) = (⟨31, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode19, subsetCodeNat19, Finset.sum_singleton]
  rw [← hc, subsetCode19Decode_left]
  simp only [c19SubsetSum]
  rw [c19SubsetSum31]
  exact (eq_inv_of_mul_eq_one_right c19InvAdjoin31).symm
#print axioms c19DecodeInv01
#print axioms c19DecodeInv31


