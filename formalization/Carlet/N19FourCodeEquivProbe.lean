import Carlet.N19FourSupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
def subsetCodeNat19Four (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode19Four (s : Finset (Fin 4)) : Fin 16 := ⟨subsetCodeNat19Four s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat19Four]
⟩
def subsetDecode19Four (m : Fin 16) : Finset (Fin 4) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode19FourDecode_left (s : Finset (Fin 4)) : subsetDecode19Four (subsetCode19Four s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode19FourDecode_right (m : Fin 16) : subsetCode19Four (subsetDecode19Four m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode19FourEquiv : Finset (Fin 4) ≃ Fin 16 where
  toFun := subsetCode19Four
  invFun := subsetDecode19Four
  left_inv := subsetCode19FourDecode_left
  right_inv := subsetCode19FourDecode_right
#print axioms subsetCode19FourEquiv




