import Carlet.N23K5SubsetSumProbe
import Carlet.N23K5CodeEquivProbe
import Carlet.N23K5InverseAdjoinProbe
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩
theorem n23K5DecodeInv01 : (n23K5SubsetSum (n23K5SubsetDecode (⟨1, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I01 := by
  have hc : n23K5SubsetCode ({0} : Finset (Fin 5)) = (⟨1, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin01).symm
theorem n23K5DecodeInv02 : (n23K5SubsetSum (n23K5SubsetDecode (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I02 := by
  have hc : n23K5SubsetCode ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin02).symm
theorem n23K5DecodeInv03 : (n23K5SubsetSum (n23K5SubsetDecode (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I03 := by
  have hc : n23K5SubsetCode ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin03).symm
theorem n23K5DecodeInv04 : (n23K5SubsetSum (n23K5SubsetDecode (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I04 := by
  have hc : n23K5SubsetCode ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin04).symm
theorem n23K5DecodeInv05 : (n23K5SubsetSum (n23K5SubsetDecode (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I05 := by
  have hc : n23K5SubsetCode ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin05).symm
theorem n23K5DecodeInv06 : (n23K5SubsetSum (n23K5SubsetDecode (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I06 := by
  have hc : n23K5SubsetCode ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin06).symm
theorem n23K5DecodeInv07 : (n23K5SubsetSum (n23K5SubsetDecode (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I07 := by
  have hc : n23K5SubsetCode ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin07).symm
theorem n23K5DecodeInv08 : (n23K5SubsetSum (n23K5SubsetDecode (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I08 := by
  have hc : n23K5SubsetCode ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin08).symm
theorem n23K5DecodeInv09 : (n23K5SubsetSum (n23K5SubsetDecode (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I09 := by
  have hc : n23K5SubsetCode ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin09).symm
theorem n23K5DecodeInv10 : (n23K5SubsetSum (n23K5SubsetDecode (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I10 := by
  have hc : n23K5SubsetCode ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin10).symm
theorem n23K5DecodeInv11 : (n23K5SubsetSum (n23K5SubsetDecode (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I11 := by
  have hc : n23K5SubsetCode ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin11).symm
theorem n23K5DecodeInv12 : (n23K5SubsetSum (n23K5SubsetDecode (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I12 := by
  have hc : n23K5SubsetCode ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin12).symm
theorem n23K5DecodeInv13 : (n23K5SubsetSum (n23K5SubsetDecode (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I13 := by
  have hc : n23K5SubsetCode ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin13).symm
theorem n23K5DecodeInv14 : (n23K5SubsetSum (n23K5SubsetDecode (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I14 := by
  have hc : n23K5SubsetCode ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin14).symm
theorem n23K5DecodeInv15 : (n23K5SubsetSum (n23K5SubsetDecode (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I15 := by
  have hc : n23K5SubsetCode ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin15).symm
theorem n23K5DecodeInv16 : (n23K5SubsetSum (n23K5SubsetDecode (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I16 := by
  have hc : n23K5SubsetCode ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum16]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin16).symm
theorem n23K5DecodeInv17 : (n23K5SubsetSum (n23K5SubsetDecode (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I17 := by
  have hc : n23K5SubsetCode ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum17]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin17).symm
theorem n23K5DecodeInv18 : (n23K5SubsetSum (n23K5SubsetDecode (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I18 := by
  have hc : n23K5SubsetCode ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum18]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin18).symm
theorem n23K5DecodeInv19 : (n23K5SubsetSum (n23K5SubsetDecode (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I19 := by
  have hc : n23K5SubsetCode ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum19]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin19).symm
theorem n23K5DecodeInv20 : (n23K5SubsetSum (n23K5SubsetDecode (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I20 := by
  have hc : n23K5SubsetCode ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum20]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin20).symm
theorem n23K5DecodeInv21 : (n23K5SubsetSum (n23K5SubsetDecode (⟨21, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I21 := by
  have hc : n23K5SubsetCode ({0,2,4} : Finset (Fin 5)) = (⟨21, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum21]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin21).symm
theorem n23K5DecodeInv22 : (n23K5SubsetSum (n23K5SubsetDecode (⟨22, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I22 := by
  have hc : n23K5SubsetCode ({1,2,4} : Finset (Fin 5)) = (⟨22, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum22]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin22).symm
theorem n23K5DecodeInv23 : (n23K5SubsetSum (n23K5SubsetDecode (⟨23, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I23 := by
  have hc : n23K5SubsetCode ({0,1,2,4} : Finset (Fin 5)) = (⟨23, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum23]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin23).symm
theorem n23K5DecodeInv24 : (n23K5SubsetSum (n23K5SubsetDecode (⟨24, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I24 := by
  have hc : n23K5SubsetCode ({3,4} : Finset (Fin 5)) = (⟨24, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum24]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin24).symm
theorem n23K5DecodeInv25 : (n23K5SubsetSum (n23K5SubsetDecode (⟨25, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I25 := by
  have hc : n23K5SubsetCode ({0,3,4} : Finset (Fin 5)) = (⟨25, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum25]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin25).symm
theorem n23K5DecodeInv26 : (n23K5SubsetSum (n23K5SubsetDecode (⟨26, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I26 := by
  have hc : n23K5SubsetCode ({1,3,4} : Finset (Fin 5)) = (⟨26, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum26]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin26).symm
theorem n23K5DecodeInv27 : (n23K5SubsetSum (n23K5SubsetDecode (⟨27, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I27 := by
  have hc : n23K5SubsetCode ({0,1,3,4} : Finset (Fin 5)) = (⟨27, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum27]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin27).symm
theorem n23K5DecodeInv28 : (n23K5SubsetSum (n23K5SubsetDecode (⟨28, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I28 := by
  have hc : n23K5SubsetCode ({2,3,4} : Finset (Fin 5)) = (⟨28, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum28]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin28).symm
theorem n23K5DecodeInv29 : (n23K5SubsetSum (n23K5SubsetDecode (⟨29, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I29 := by
  have hc : n23K5SubsetCode ({0,2,3,4} : Finset (Fin 5)) = (⟨29, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum29]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin29).symm
theorem n23K5DecodeInv30 : (n23K5SubsetSum (n23K5SubsetDecode (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I30 := by
  have hc : n23K5SubsetCode ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum30]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin30).symm
theorem n23K5DecodeInv31 : (n23K5SubsetSum (n23K5SubsetDecode (⟨31, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f23 n23K5I31 := by
  have hc : n23K5SubsetCode ({0,1,2,3,4} : Finset (Fin 5)) = (⟨31, by omega⟩ : Fin 32) := by
    apply n23K5SubsetCodeEquiv.symm.injective
    change n23K5SubsetDecode (n23K5SubsetCode _ ) = n23K5SubsetDecode _
    rw [n23K5SubsetCodeDecode_left]
    decide
  rw [← hc, n23K5SubsetCodeDecode_left]
  simp only [n23K5SubsetSum]
  rw [n23K5SubsetSum31]
  exact (eq_inv_of_mul_eq_one_right n23K5InvAdjoin31).symm
#print axioms n23K5DecodeInv01
#print axioms n23K5DecodeInv31
