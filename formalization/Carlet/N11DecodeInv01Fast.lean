import Carlet.N11CodeEquivProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
theorem certDecodeInv01_fast :
    (certSubsetSum (subsetDecode (1 : Fin 32)))⁻¹ = AdjoinRoot.mk f certI01 := by
  have hc : subsetCode ({0} : Finset (Fin 5)) = (1 : Fin 32) := by
    norm_num [subsetCode, subsetCodeNat]
  rw [← hc, subsetCodeDecode_left]
  simp only [certSubsetSum]
  rw [certSubsetSum01]
  exact (eq_inv_of_mul_eq_one_left certInvAdjoin01).symm
#print axioms certDecodeInv01_fast


