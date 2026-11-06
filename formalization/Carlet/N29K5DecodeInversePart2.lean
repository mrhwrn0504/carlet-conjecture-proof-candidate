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
theorem n29K5DecodeInv06 : (n29K5SubsetSum (n29K5SubsetDecode (⟨6, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I06 := by
  have hc : n29K5SubsetCode ({1,2} : Finset (Fin 5)) = (⟨6, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum06]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin06).symm
theorem n29K5DecodeInv07 : (n29K5SubsetSum (n29K5SubsetDecode (⟨7, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I07 := by
  have hc : n29K5SubsetCode ({0,1,2} : Finset (Fin 5)) = (⟨7, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum07]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin07).symm
theorem n29K5DecodeInv08 : (n29K5SubsetSum (n29K5SubsetDecode (⟨8, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I08 := by
  have hc : n29K5SubsetCode ({3} : Finset (Fin 5)) = (⟨8, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum08]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin08).symm
theorem n29K5DecodeInv09 : (n29K5SubsetSum (n29K5SubsetDecode (⟨9, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I09 := by
  have hc : n29K5SubsetCode ({0,3} : Finset (Fin 5)) = (⟨9, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum09]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin09).symm
theorem n29K5DecodeInv10 : (n29K5SubsetSum (n29K5SubsetDecode (⟨10, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I10 := by
  have hc : n29K5SubsetCode ({1,3} : Finset (Fin 5)) = (⟨10, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum10]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin10).symm
#print axioms n29K5DecodeInv06
#print axioms n29K5DecodeInv10
