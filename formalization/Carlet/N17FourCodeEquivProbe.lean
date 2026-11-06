import Carlet.N17FourSupportLinearProbe
import Mathlib.Tactic
noncomputable section
open Polynomial
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
def subsetCodeNat17Four (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, 2^i.val
def subsetCode17Four (s : Finset (Fin 4)) : Fin 16 := ⟨subsetCodeNat17Four s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat17Four]
⟩
def subsetDecode17Four (m : Fin 16) : Finset (Fin 4) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCode17FourDecode_left (s : Finset (Fin 4)) : subsetDecode17Four (subsetCode17Four s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCode17FourDecode_right (m : Fin 16) : subsetCode17Four (subsetDecode17Four m) = m := by
  classical
  fin_cases m <;> decide
def subsetCode17FourEquiv : Finset (Fin 4) ≃ Fin 16 where
  toFun := subsetCode17Four
  invFun := subsetDecode17Four
  left_inv := subsetCode17FourDecode_left
  right_inv := subsetCode17FourDecode_right
#print axioms subsetCode17FourEquiv




