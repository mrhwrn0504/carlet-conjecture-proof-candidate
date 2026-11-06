import Carlet.N13K4SubsetSums
import Mathlib.Tactic
noncomputable section
namespace N13K4
def subsetCodeNat (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, 2 ^ i.val
def subsetCode (s : Finset (Fin 4)) : Fin 16 := ⟨subsetCodeNat s, by
  classical
  fin_cases s <;> norm_num [subsetCodeNat]
⟩
def subsetDecode (m : Fin 16) : Finset (Fin 4) := Finset.univ.filter (fun i => Nat.testBit m.val i.val)
theorem subsetCodeDecode_left (s : Finset (Fin 4)) : subsetDecode (subsetCode s) = s := by
  classical
  fin_cases s <;> decide
theorem subsetCodeDecode_right (m : Fin 16) : subsetCode (subsetDecode m) = m := by
  classical
  fin_cases m <;> decide
def subsetCodeEquiv : Finset (Fin 4) ≃ Fin 16 where
  toFun := subsetCode
  invFun := subsetDecode
  left_inv := subsetCodeDecode_left
  right_inv := subsetCodeDecode_right
#print axioms subsetCodeEquiv
end N13K4
