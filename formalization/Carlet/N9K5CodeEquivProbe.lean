import Carlet.N9K5InverseAdjoinProbe
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false

noncomputable section
open Polynomial
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩

def n9K5SubsetCodeNat (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val

def n9K5SubsetCode (s : Finset (Fin 5)) : Fin 32 := ⟨n9K5SubsetCodeNat s, by
  classical
  fin_cases s <;> norm_num [n9K5SubsetCodeNat]
⟩

def n9K5SubsetDecode (m : Fin 32) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => Nat.testBit m.val i.val)

theorem n9K5SubsetCodeDecode_left (s : Finset (Fin 5)) :
    n9K5SubsetDecode (n9K5SubsetCode s) = s := by
  classical
  fin_cases s <;> decide

theorem n9K5SubsetCodeDecode_right (m : Fin 32) :
    n9K5SubsetCode (n9K5SubsetDecode m) = m := by
  classical
  fin_cases m <;> decide

def n9K5SubsetCodeEquiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := n9K5SubsetCode
  invFun := n9K5SubsetDecode
  left_inv := n9K5SubsetCodeDecode_left
  right_inv := n9K5SubsetCodeDecode_right

#print axioms n9K5SubsetCodeEquiv
