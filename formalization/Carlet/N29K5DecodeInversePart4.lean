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
theorem n29K5DecodeInv16 : (n29K5SubsetSum (n29K5SubsetDecode (⟨16, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I16 := by
  have hc : n29K5SubsetCode ({4} : Finset (Fin 5)) = (⟨16, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum16]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin16).symm
theorem n29K5DecodeInv17 : (n29K5SubsetSum (n29K5SubsetDecode (⟨17, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I17 := by
  have hc : n29K5SubsetCode ({0,4} : Finset (Fin 5)) = (⟨17, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum17]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin17).symm
theorem n29K5DecodeInv18 : (n29K5SubsetSum (n29K5SubsetDecode (⟨18, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I18 := by
  have hc : n29K5SubsetCode ({1,4} : Finset (Fin 5)) = (⟨18, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum18]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin18).symm
theorem n29K5DecodeInv19 : (n29K5SubsetSum (n29K5SubsetDecode (⟨19, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I19 := by
  have hc : n29K5SubsetCode ({0,1,4} : Finset (Fin 5)) = (⟨19, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum19]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin19).symm
theorem n29K5DecodeInv20 : (n29K5SubsetSum (n29K5SubsetDecode (⟨20, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I20 := by
  have hc : n29K5SubsetCode ({2,4} : Finset (Fin 5)) = (⟨20, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum20]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin20).symm
#print axioms n29K5DecodeInv16
#print axioms n29K5DecodeInv20
