import Carlet.N17CodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
theorem c17DecodeInv01 : (c17SubsetSum (subsetDecode17 (⟨1, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I01 := by
  have hc : subsetCode17 ({0} : Finset (Fin 5)) = (⟨1, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin01).symm
theorem c17DecodeInv02 : (c17SubsetSum (subsetDecode17 (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I02 := by
  have hc : subsetCode17 ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin02).symm
theorem c17DecodeInv03 : (c17SubsetSum (subsetDecode17 (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I03 := by
  have hc : subsetCode17 ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin03).symm
theorem c17DecodeInv04 : (c17SubsetSum (subsetDecode17 (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I04 := by
  have hc : subsetCode17 ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin04).symm
theorem c17DecodeInv05 : (c17SubsetSum (subsetDecode17 (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I05 := by
  have hc : subsetCode17 ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin05).symm
theorem c17DecodeInv06 : (c17SubsetSum (subsetDecode17 (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I06 := by
  have hc : subsetCode17 ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin06).symm
theorem c17DecodeInv07 : (c17SubsetSum (subsetDecode17 (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I07 := by
  have hc : subsetCode17 ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin07).symm
theorem c17DecodeInv08 : (c17SubsetSum (subsetDecode17 (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I08 := by
  have hc : subsetCode17 ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin08).symm
theorem c17DecodeInv09 : (c17SubsetSum (subsetDecode17 (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I09 := by
  have hc : subsetCode17 ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin09).symm
theorem c17DecodeInv10 : (c17SubsetSum (subsetDecode17 (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I10 := by
  have hc : subsetCode17 ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin10).symm
theorem c17DecodeInv11 : (c17SubsetSum (subsetDecode17 (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I11 := by
  have hc : subsetCode17 ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin11).symm
theorem c17DecodeInv12 : (c17SubsetSum (subsetDecode17 (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I12 := by
  have hc : subsetCode17 ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin12).symm
theorem c17DecodeInv13 : (c17SubsetSum (subsetDecode17 (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I13 := by
  have hc : subsetCode17 ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin13).symm
theorem c17DecodeInv14 : (c17SubsetSum (subsetDecode17 (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I14 := by
  have hc : subsetCode17 ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin14).symm
theorem c17DecodeInv15 : (c17SubsetSum (subsetDecode17 (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I15 := by
  have hc : subsetCode17 ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin15).symm
theorem c17DecodeInv16 : (c17SubsetSum (subsetDecode17 (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I16 := by
  have hc : subsetCode17 ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum16]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin16).symm
theorem c17DecodeInv17 : (c17SubsetSum (subsetDecode17 (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I17 := by
  have hc : subsetCode17 ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum17]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin17).symm
theorem c17DecodeInv18 : (c17SubsetSum (subsetDecode17 (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I18 := by
  have hc : subsetCode17 ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum18]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin18).symm
theorem c17DecodeInv19 : (c17SubsetSum (subsetDecode17 (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I19 := by
  have hc : subsetCode17 ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum19]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin19).symm
theorem c17DecodeInv20 : (c17SubsetSum (subsetDecode17 (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I20 := by
  have hc : subsetCode17 ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum20]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin20).symm
theorem c17DecodeInv21 : (c17SubsetSum (subsetDecode17 (⟨21, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I21 := by
  have hc : subsetCode17 ({0,2,4} : Finset (Fin 5)) = (⟨21, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum21]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin21).symm
theorem c17DecodeInv22 : (c17SubsetSum (subsetDecode17 (⟨22, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I22 := by
  have hc : subsetCode17 ({1,2,4} : Finset (Fin 5)) = (⟨22, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum22]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin22).symm
theorem c17DecodeInv23 : (c17SubsetSum (subsetDecode17 (⟨23, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I23 := by
  have hc : subsetCode17 ({0,1,2,4} : Finset (Fin 5)) = (⟨23, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum23]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin23).symm
theorem c17DecodeInv24 : (c17SubsetSum (subsetDecode17 (⟨24, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I24 := by
  have hc : subsetCode17 ({3,4} : Finset (Fin 5)) = (⟨24, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum24]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin24).symm
theorem c17DecodeInv25 : (c17SubsetSum (subsetDecode17 (⟨25, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I25 := by
  have hc : subsetCode17 ({0,3,4} : Finset (Fin 5)) = (⟨25, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum25]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin25).symm
theorem c17DecodeInv26 : (c17SubsetSum (subsetDecode17 (⟨26, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I26 := by
  have hc : subsetCode17 ({1,3,4} : Finset (Fin 5)) = (⟨26, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum26]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin26).symm
theorem c17DecodeInv27 : (c17SubsetSum (subsetDecode17 (⟨27, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I27 := by
  have hc : subsetCode17 ({0,1,3,4} : Finset (Fin 5)) = (⟨27, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum27]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin27).symm
theorem c17DecodeInv28 : (c17SubsetSum (subsetDecode17 (⟨28, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I28 := by
  have hc : subsetCode17 ({2,3,4} : Finset (Fin 5)) = (⟨28, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum28]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin28).symm
theorem c17DecodeInv29 : (c17SubsetSum (subsetDecode17 (⟨29, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I29 := by
  have hc : subsetCode17 ({0,2,3,4} : Finset (Fin 5)) = (⟨29, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum29]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin29).symm
theorem c17DecodeInv30 : (c17SubsetSum (subsetDecode17 (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I30 := by
  have hc : subsetCode17 ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum30]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin30).symm
theorem c17DecodeInv31 : (c17SubsetSum (subsetDecode17 (⟨31, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f17 c17I31 := by
  have hc : subsetCode17 ({0,1,2,3,4} : Finset (Fin 5)) = (⟨31, by omega⟩ : Fin 32) := by
    apply Fin.ext
    simp [subsetCode17, subsetCodeNat17, Finset.sum_singleton]
  rw [← hc, subsetCode17Decode_left]
  simp only [c17SubsetSum]
  rw [c17SubsetSum31]
  exact (eq_inv_of_mul_eq_one_right c17InvAdjoin31).symm
#print axioms c17DecodeInv01
#print axioms c17DecodeInv31


