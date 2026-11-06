import Carlet.N11SupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
def subsetCodeNat (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode (s : Finset (Fin 5)) : Fin 32 := ⟨subsetCodeNat s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat]
⟩
def subsetDecode (m : Fin 32) : Finset (Fin 5) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCodeDecode_left (s : Finset (Fin 5)) : subsetDecode (subsetCode s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCodeDecode_right (m : Fin 32) : subsetCode (subsetDecode m) = m := by
  classical
  fin_cases m <;> decide
def subsetCodeEquiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := subsetCode
  invFun := subsetDecode
  left_inv := subsetCodeDecode_left
  right_inv := subsetCodeDecode_right
#print axioms subsetCodeEquiv


