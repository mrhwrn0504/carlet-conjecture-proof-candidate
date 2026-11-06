import Carlet.N9SupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
def subsetCodeNat9 (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode9 (s : Finset (Fin 4)) : Fin 16 := ⟨subsetCodeNat9 s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat9]
⟩
def subsetDecode9 (m : Fin 16) : Finset (Fin 4) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode9Decode_left (s : Finset (Fin 4)) : subsetDecode9 (subsetCode9 s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode9Decode_right (m : Fin 16) : subsetCode9 (subsetDecode9 m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode9Equiv : Finset (Fin 4) ≃ Fin 16 where
  toFun := subsetCode9
  invFun := subsetDecode9
  left_inv := subsetCode9Decode_left
  right_inv := subsetCode9Decode_right
#print axioms subsetCode9Equiv




