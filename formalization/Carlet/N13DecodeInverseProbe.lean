import Carlet.N13CodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
theorem cert13DecodeInv01 : (cert13SubsetSum (subsetDecode13 (⟨1, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I01 := by
  have hc : subsetCode13 ({0} : Finset (Fin 5)) = (⟨1, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin01).symm
theorem cert13DecodeInv02 : (cert13SubsetSum (subsetDecode13 (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I02 := by
  have hc : subsetCode13 ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin02).symm
theorem cert13DecodeInv03 : (cert13SubsetSum (subsetDecode13 (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I03 := by
  have hc : subsetCode13 ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin03).symm
theorem cert13DecodeInv04 : (cert13SubsetSum (subsetDecode13 (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I04 := by
  have hc : subsetCode13 ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin04).symm
theorem cert13DecodeInv05 : (cert13SubsetSum (subsetDecode13 (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I05 := by
  have hc : subsetCode13 ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin05).symm
theorem cert13DecodeInv06 : (cert13SubsetSum (subsetDecode13 (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I06 := by
  have hc : subsetCode13 ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin06).symm
theorem cert13DecodeInv07 : (cert13SubsetSum (subsetDecode13 (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I07 := by
  have hc : subsetCode13 ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin07).symm
theorem cert13DecodeInv08 : (cert13SubsetSum (subsetDecode13 (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I08 := by
  have hc : subsetCode13 ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin08).symm
theorem cert13DecodeInv09 : (cert13SubsetSum (subsetDecode13 (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I09 := by
  have hc : subsetCode13 ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin09).symm
theorem cert13DecodeInv10 : (cert13SubsetSum (subsetDecode13 (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I10 := by
  have hc : subsetCode13 ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin10).symm
theorem cert13DecodeInv11 : (cert13SubsetSum (subsetDecode13 (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I11 := by
  have hc : subsetCode13 ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin11).symm
theorem cert13DecodeInv12 : (cert13SubsetSum (subsetDecode13 (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I12 := by
  have hc : subsetCode13 ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin12).symm
theorem cert13DecodeInv13 : (cert13SubsetSum (subsetDecode13 (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I13 := by
  have hc : subsetCode13 ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin13).symm
theorem cert13DecodeInv14 : (cert13SubsetSum (subsetDecode13 (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I14 := by
  have hc : subsetCode13 ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin14).symm
theorem cert13DecodeInv15 : (cert13SubsetSum (subsetDecode13 (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I15 := by
  have hc : subsetCode13 ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin15).symm
theorem cert13DecodeInv16 : (cert13SubsetSum (subsetDecode13 (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I16 := by
  have hc : subsetCode13 ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum16]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin16).symm
theorem cert13DecodeInv17 : (cert13SubsetSum (subsetDecode13 (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I17 := by
  have hc : subsetCode13 ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum17]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin17).symm
theorem cert13DecodeInv18 : (cert13SubsetSum (subsetDecode13 (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I18 := by
  have hc : subsetCode13 ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum18]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin18).symm
theorem cert13DecodeInv19 : (cert13SubsetSum (subsetDecode13 (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I19 := by
  have hc : subsetCode13 ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum19]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin19).symm
theorem cert13DecodeInv20 : (cert13SubsetSum (subsetDecode13 (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I20 := by
  have hc : subsetCode13 ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum20]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin20).symm
theorem cert13DecodeInv21 : (cert13SubsetSum (subsetDecode13 (⟨21, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I21 := by
  have hc : subsetCode13 ({0,2,4} : Finset (Fin 5)) = (⟨21, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum21]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin21).symm
theorem cert13DecodeInv22 : (cert13SubsetSum (subsetDecode13 (⟨22, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I22 := by
  have hc : subsetCode13 ({1,2,4} : Finset (Fin 5)) = (⟨22, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum22]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin22).symm
theorem cert13DecodeInv23 : (cert13SubsetSum (subsetDecode13 (⟨23, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I23 := by
  have hc : subsetCode13 ({0,1,2,4} : Finset (Fin 5)) = (⟨23, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum23]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin23).symm
theorem cert13DecodeInv24 : (cert13SubsetSum (subsetDecode13 (⟨24, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I24 := by
  have hc : subsetCode13 ({3,4} : Finset (Fin 5)) = (⟨24, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum24]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin24).symm
theorem cert13DecodeInv25 : (cert13SubsetSum (subsetDecode13 (⟨25, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I25 := by
  have hc : subsetCode13 ({0,3,4} : Finset (Fin 5)) = (⟨25, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum25]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin25).symm
theorem cert13DecodeInv26 : (cert13SubsetSum (subsetDecode13 (⟨26, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I26 := by
  have hc : subsetCode13 ({1,3,4} : Finset (Fin 5)) = (⟨26, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum26]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin26).symm
theorem cert13DecodeInv27 : (cert13SubsetSum (subsetDecode13 (⟨27, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I27 := by
  have hc : subsetCode13 ({0,1,3,4} : Finset (Fin 5)) = (⟨27, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum27]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin27).symm
theorem cert13DecodeInv28 : (cert13SubsetSum (subsetDecode13 (⟨28, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I28 := by
  have hc : subsetCode13 ({2,3,4} : Finset (Fin 5)) = (⟨28, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum28]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin28).symm
theorem cert13DecodeInv29 : (cert13SubsetSum (subsetDecode13 (⟨29, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I29 := by
  have hc : subsetCode13 ({0,2,3,4} : Finset (Fin 5)) = (⟨29, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum29]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin29).symm
theorem cert13DecodeInv30 : (cert13SubsetSum (subsetDecode13 (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I30 := by
  have hc : subsetCode13 ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum30]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin30).symm
theorem cert13DecodeInv31 : (cert13SubsetSum (subsetDecode13 (⟨31, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I31 := by
  have hc : subsetCode13 ({0,1,2,3,4} : Finset (Fin 5)) = (⟨31, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode13, subsetCodeNat13, Finset.sum_singleton]
  rw [← hc, subsetCode13Decode_left]
  simp only [cert13SubsetSum]
  rw [cert13SubsetSum31]
  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin31).symm
#print axioms cert13DecodeInv01
#print axioms cert13DecodeInv31


