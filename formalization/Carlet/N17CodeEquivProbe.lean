import Carlet.N17SupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
def subsetCodeNat17 (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode17 (s : Finset (Fin 5)) : Fin 32 := ⟨subsetCodeNat17 s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat17]
⟩
def subsetDecode17 (m : Fin 32) : Finset (Fin 5) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode17Decode_left (s : Finset (Fin 5)) : subsetDecode17 (subsetCode17 s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode17Decode_right (m : Fin 32) : subsetCode17 (subsetDecode17 m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode17Equiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := subsetCode17
  invFun := subsetDecode17
  left_inv := subsetCode17Decode_left
  right_inv := subsetCode17Decode_right
#print axioms subsetCode17Equiv




