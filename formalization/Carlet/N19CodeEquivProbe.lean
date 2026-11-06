import Carlet.N19SupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
def subsetCodeNat19 (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode19 (s : Finset (Fin 5)) : Fin 32 := ⟨subsetCodeNat19 s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat19]
⟩
def subsetDecode19 (m : Fin 32) : Finset (Fin 5) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode19Decode_left (s : Finset (Fin 5)) : subsetDecode19 (subsetCode19 s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode19Decode_right (m : Fin 32) : subsetCode19 (subsetDecode19 m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode19Equiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := subsetCode19
  invFun := subsetDecode19
  left_inv := subsetCode19Decode_left
  right_inv := subsetCode19Decode_right
#print axioms subsetCode19Equiv




