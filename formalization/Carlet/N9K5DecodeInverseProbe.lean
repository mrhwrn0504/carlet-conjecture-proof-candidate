import Carlet.N9K5SubsetSumProbe
import Carlet.N9K5CodeEquivProbe
import Carlet.N9K5InverseAdjoinProbe
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
theorem n9K5DecodeInv01 : (n9K5SubsetSum (n9K5SubsetDecode (⟨1, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I01 := by
  have hc : n9K5SubsetCode ({0} : Finset (Fin 5)) = (⟨1, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin01).symm
theorem n9K5DecodeInv02 : (n9K5SubsetSum (n9K5SubsetDecode (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I02 := by
  have hc : n9K5SubsetCode ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin02).symm
theorem n9K5DecodeInv03 : (n9K5SubsetSum (n9K5SubsetDecode (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I03 := by
  have hc : n9K5SubsetCode ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin03).symm
theorem n9K5DecodeInv04 : (n9K5SubsetSum (n9K5SubsetDecode (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I04 := by
  have hc : n9K5SubsetCode ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin04).symm
theorem n9K5DecodeInv05 : (n9K5SubsetSum (n9K5SubsetDecode (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I05 := by
  have hc : n9K5SubsetCode ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin05).symm
theorem n9K5DecodeInv06 : (n9K5SubsetSum (n9K5SubsetDecode (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I06 := by
  have hc : n9K5SubsetCode ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin06).symm
theorem n9K5DecodeInv07 : (n9K5SubsetSum (n9K5SubsetDecode (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I07 := by
  have hc : n9K5SubsetCode ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin07).symm
theorem n9K5DecodeInv08 : (n9K5SubsetSum (n9K5SubsetDecode (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I08 := by
  have hc : n9K5SubsetCode ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin08).symm
theorem n9K5DecodeInv09 : (n9K5SubsetSum (n9K5SubsetDecode (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I09 := by
  have hc : n9K5SubsetCode ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin09).symm
theorem n9K5DecodeInv10 : (n9K5SubsetSum (n9K5SubsetDecode (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I10 := by
  have hc : n9K5SubsetCode ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin10).symm
theorem n9K5DecodeInv11 : (n9K5SubsetSum (n9K5SubsetDecode (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I11 := by
  have hc : n9K5SubsetCode ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin11).symm
theorem n9K5DecodeInv12 : (n9K5SubsetSum (n9K5SubsetDecode (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I12 := by
  have hc : n9K5SubsetCode ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin12).symm
theorem n9K5DecodeInv13 : (n9K5SubsetSum (n9K5SubsetDecode (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I13 := by
  have hc : n9K5SubsetCode ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin13).symm
theorem n9K5DecodeInv14 : (n9K5SubsetSum (n9K5SubsetDecode (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I14 := by
  have hc : n9K5SubsetCode ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin14).symm
theorem n9K5DecodeInv15 : (n9K5SubsetSum (n9K5SubsetDecode (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I15 := by
  have hc : n9K5SubsetCode ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin15).symm
theorem n9K5DecodeInv16 : (n9K5SubsetSum (n9K5SubsetDecode (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I16 := by
  have hc : n9K5SubsetCode ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum16]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin16).symm
theorem n9K5DecodeInv17 : (n9K5SubsetSum (n9K5SubsetDecode (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I17 := by
  have hc : n9K5SubsetCode ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum17]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin17).symm
theorem n9K5DecodeInv18 : (n9K5SubsetSum (n9K5SubsetDecode (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I18 := by
  have hc : n9K5SubsetCode ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum18]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin18).symm
theorem n9K5DecodeInv19 : (n9K5SubsetSum (n9K5SubsetDecode (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I19 := by
  have hc : n9K5SubsetCode ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum19]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin19).symm
theorem n9K5DecodeInv20 : (n9K5SubsetSum (n9K5SubsetDecode (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I20 := by
  have hc : n9K5SubsetCode ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum20]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin20).symm
theorem n9K5DecodeInv21 : (n9K5SubsetSum (n9K5SubsetDecode (⟨21, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I21 := by
  have hc : n9K5SubsetCode ({0,2,4} : Finset (Fin 5)) = (⟨21, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum21]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin21).symm
theorem n9K5DecodeInv22 : (n9K5SubsetSum (n9K5SubsetDecode (⟨22, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I22 := by
  have hc : n9K5SubsetCode ({1,2,4} : Finset (Fin 5)) = (⟨22, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum22]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin22).symm
theorem n9K5DecodeInv23 : (n9K5SubsetSum (n9K5SubsetDecode (⟨23, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I23 := by
  have hc : n9K5SubsetCode ({0,1,2,4} : Finset (Fin 5)) = (⟨23, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum23]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin23).symm
theorem n9K5DecodeInv24 : (n9K5SubsetSum (n9K5SubsetDecode (⟨24, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I24 := by
  have hc : n9K5SubsetCode ({3,4} : Finset (Fin 5)) = (⟨24, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum24]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin24).symm
theorem n9K5DecodeInv25 : (n9K5SubsetSum (n9K5SubsetDecode (⟨25, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I25 := by
  have hc : n9K5SubsetCode ({0,3,4} : Finset (Fin 5)) = (⟨25, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum25]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin25).symm
theorem n9K5DecodeInv26 : (n9K5SubsetSum (n9K5SubsetDecode (⟨26, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I26 := by
  have hc : n9K5SubsetCode ({1,3,4} : Finset (Fin 5)) = (⟨26, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum26]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin26).symm
theorem n9K5DecodeInv27 : (n9K5SubsetSum (n9K5SubsetDecode (⟨27, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I27 := by
  have hc : n9K5SubsetCode ({0,1,3,4} : Finset (Fin 5)) = (⟨27, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum27]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin27).symm
theorem n9K5DecodeInv28 : (n9K5SubsetSum (n9K5SubsetDecode (⟨28, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I28 := by
  have hc : n9K5SubsetCode ({2,3,4} : Finset (Fin 5)) = (⟨28, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum28]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin28).symm
theorem n9K5DecodeInv29 : (n9K5SubsetSum (n9K5SubsetDecode (⟨29, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I29 := by
  have hc : n9K5SubsetCode ({0,2,3,4} : Finset (Fin 5)) = (⟨29, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum29]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin29).symm
theorem n9K5DecodeInv30 : (n9K5SubsetSum (n9K5SubsetDecode (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I30 := by
  have hc : n9K5SubsetCode ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum30]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin30).symm
theorem n9K5DecodeInv31 : (n9K5SubsetSum (n9K5SubsetDecode (⟨31, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f9 n9K5I31 := by
  have hc : n9K5SubsetCode ({0,1,2,3,4} : Finset (Fin 5)) = (⟨31, by omega⟩ : Fin 32) := by
    apply n9K5SubsetCodeEquiv.symm.injective
    change n9K5SubsetDecode (n9K5SubsetCode _ ) = n9K5SubsetDecode _
    rw [n9K5SubsetCodeDecode_left]
    decide
  rw [← hc, n9K5SubsetCodeDecode_left]
  simp only [n9K5SubsetSum]
  rw [n9K5SubsetSum31]
  exact (eq_inv_of_mul_eq_one_right n9K5InvAdjoin31).symm
#print axioms n9K5DecodeInv01
#print axioms n9K5DecodeInv31
