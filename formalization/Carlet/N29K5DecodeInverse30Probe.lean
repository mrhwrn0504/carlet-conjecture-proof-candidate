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
theorem n29K5DecodeInv30 : (n29K5SubsetSum (n29K5SubsetDecode (⟨30, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f29K5 n29K5I30 := by
  have hc : n29K5SubsetCode ({1,2,3,4} : Finset (Fin 5)) = (⟨30, by omega⟩ : Fin 32) := by
    apply n29K5SubsetCodeEquiv.symm.injective
    change n29K5SubsetDecode (n29K5SubsetCode _ ) = n29K5SubsetDecode _
    rw [n29K5SubsetCodeDecode_left]
    decide
  rw [← hc, n29K5SubsetCodeDecode_left]
  simp only [n29K5SubsetSum]
  rw [n29K5SubsetSum30]
  exact (eq_inv_of_mul_eq_one_right n29K5InvAdjoin30).symm
#print axioms n29K5DecodeInv30
