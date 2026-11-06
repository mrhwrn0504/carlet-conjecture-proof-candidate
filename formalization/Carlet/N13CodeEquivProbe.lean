import Carlet.N13SupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
def subsetCodeNat13 (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode13 (s : Finset (Fin 5)) : Fin 32 := ⟨subsetCodeNat13 s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat13]
⟩
def subsetDecode13 (m : Fin 32) : Finset (Fin 5) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode13Decode_left (s : Finset (Fin 5)) : subsetDecode13 (subsetCode13 s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode13Decode_right (m : Fin 32) : subsetCode13 (subsetDecode13 m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode13Equiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := subsetCode13
  invFun := subsetDecode13
  left_inv := subsetCode13Decode_left
  right_inv := subsetCode13Decode_right
#print axioms subsetCode13Equiv




