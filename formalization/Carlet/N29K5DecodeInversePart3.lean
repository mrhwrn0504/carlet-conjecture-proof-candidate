import Carlet.N29K5SubsetSumProbe
import Carlet.N29K5CodeEquivProbe
import Carlet.N29K5InverseAdjoinProbe
import Mathlib.Tactic
open Carlet
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000
local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩
theorem n29K5DecodeInv11 : (n29K5SubsetSum (n29K5SubsetDecode (⟨11, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I11 := by
  have hc : n29K5SubsetCode ({0,1,3} : Finset (Fin 5)) = (⟨11, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum11]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin11).symm
theorem n29K5DecodeInv12 : (n29K5SubsetSum (n29K5SubsetDecode (⟨12, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I12 := by
  have hc : n29K5SubsetCode ({2,3} : Finset (Fin 5)) = (⟨12, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum12]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin12).symm
theorem n29K5DecodeInv13 : (n29K5SubsetSum (n29K5SubsetDecode (⟨13, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I13 := by
  have hc : n29K5SubsetCode ({0,2,3} : Finset (Fin 5)) = (⟨13, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum13]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin13).symm
theorem n29K5DecodeInv14 : (n29K5SubsetSum (n29K5SubsetDecode (⟨14, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I14 := by
  have hc : n29K5SubsetCode ({1,2,3} : Finset (Fin 5)) = (⟨14, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum14]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin14).symm
theorem n29K5DecodeInv15 : (n29K5SubsetSum (n29K5SubsetDecode (⟨15, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I15 := by
  have hc : n29K5SubsetCode ({0,1,2,3} : Finset (Fin 5)) = (⟨15, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum15]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin15).symm
#print axioms n29K5DecodeInv11
#print axioms n29K5DecodeInv15
