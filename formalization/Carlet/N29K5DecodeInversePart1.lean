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
theorem n29K5DecodeInv01 : (n29K5SubsetSum (n29K5SubsetDecode (⟨1, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I01 := by
  have hc : n29K5SubsetCode ({0} : Finset (Fin 5)) = (⟨1, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum01]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin01).symm
theorem n29K5DecodeInv02 : (n29K5SubsetSum (n29K5SubsetDecode (⟨2, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I02 := by
  have hc : n29K5SubsetCode ({1} : Finset (Fin 5)) = (⟨2, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum02]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin02).symm
theorem n29K5DecodeInv03 : (n29K5SubsetSum (n29K5SubsetDecode (⟨3, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I03 := by
  have hc : n29K5SubsetCode ({0,1} : Finset (Fin 5)) = (⟨3, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum03]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin03).symm
theorem n29K5DecodeInv04 : (n29K5SubsetSum (n29K5SubsetDecode (⟨4, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I04 := by
  have hc : n29K5SubsetCode ({2} : Finset (Fin 5)) = (⟨4, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum04]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin04).symm
theorem n29K5DecodeInv05 : (n29K5SubsetSum (n29K5SubsetDecode (⟨5, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I05 := by
  have hc : n29K5SubsetCode ({0,2} : Finset (Fin 5)) = (⟨5, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum05]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin05).symm
#print axioms n29K5DecodeInv01
#print axioms n29K5DecodeInv05
