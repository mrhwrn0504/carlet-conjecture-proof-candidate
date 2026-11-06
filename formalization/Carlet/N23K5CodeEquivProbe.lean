import Carlet.N23K5InverseAdjoinProbe
set_option linter.unnecessarySeqFocus false

noncomputable section
open Polynomial
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩

def n23K5SubsetCodeNat (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val

def n23K5SubsetCode (s : Finset (Fin 5)) : Fin 32 := ⟨n23K5SubsetCodeNat s, by
  classical
  fin_cases s <;> norm_num [n23K5SubsetCodeNat]
⟩

def n23K5SubsetDecode (m : Fin 32) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => Nat.testBit m.val i.val)

theorem n23K5SubsetCodeDecode_left (s : Finset (Fin 5)) :
    n23K5SubsetDecode (n23K5SubsetCode s) = s := by
  classical
  fin_cases s <;> decide

theorem n23K5SubsetCodeDecode_right (m : Fin 32) :
    n23K5SubsetCode (n23K5SubsetDecode m) = m := by
  classical
  fin_cases m <;> decide

def n23K5SubsetCodeEquiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := n23K5SubsetCode
  invFun := n23K5SubsetDecode
  left_inv := n23K5SubsetCodeDecode_left
  right_inv := n23K5SubsetCodeDecode_right

#print axioms n23K5SubsetCodeEquiv
