import Carlet.N29K5InverseAdjoinProbe
open Carlet
set_option linter.unnecessarySeqFocus false

noncomputable section
set_option maxHeartbeats 4000000
open Polynomial
local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩

def n29K5SubsetCodeNat (s : Finset (Fin 5)) : ℕ := ∑ i ∈ s, 2^i.val

def n29K5SubsetCode (s : Finset (Fin 5)) : Fin 32 := ⟨n29K5SubsetCodeNat s, by
  classical
  fin_cases s <;> norm_num [n29K5SubsetCodeNat]
⟩

def n29K5SubsetDecode (m : Fin 32) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => Nat.testBit m.val i.val)

theorem n29K5SubsetCodeDecode_left (s : Finset (Fin 5)) :
    n29K5SubsetDecode (n29K5SubsetCode s) = s := by
  classical
  fin_cases s <;> decide

theorem n29K5SubsetCodeDecode_right (m : Fin 32) :
    n29K5SubsetCode (n29K5SubsetDecode m) = m := by
  classical
  fin_cases m <;> decide

def n29K5SubsetCodeEquiv : Finset (Fin 5) ≃ Fin 32 where
  toFun := n29K5SubsetCode
  invFun := n29K5SubsetDecode
  left_inv := n29K5SubsetCodeDecode_left
  right_inv := n29K5SubsetCodeDecode_right

#print axioms n29K5SubsetCodeEquiv
