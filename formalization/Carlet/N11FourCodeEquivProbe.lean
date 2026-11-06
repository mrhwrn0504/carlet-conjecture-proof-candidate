import Carlet.N11FourSupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
def subsetCodeNat11Four (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode11Four (s : Finset (Fin 4)) : Fin 16 := ⟨subsetCodeNat11Four s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat11Four]
⟩
def subsetDecode11Four (m : Fin 16) : Finset (Fin 4) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode11FourDecode_left (s : Finset (Fin 4)) : subsetDecode11Four (subsetCode11Four s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode11FourDecode_right (m : Fin 16) : subsetCode11Four (subsetDecode11Four m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode11FourEquiv : Finset (Fin 4) ≃ Fin 16 where
  toFun := subsetCode11Four
  invFun := subsetDecode11Four
  left_inv := subsetCode11FourDecode_left
  right_inv := subsetCode11FourDecode_right
#print axioms subsetCode11FourEquiv




