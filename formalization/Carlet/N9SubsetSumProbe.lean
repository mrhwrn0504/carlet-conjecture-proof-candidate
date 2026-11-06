import Carlet.N9ComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
def d9BasePoly : Fin 4 → P17
| 0 => d9V01
| 1 => d9V02
| 2 => d9V04
| 3 => d9V08
def d9Base (i : Fin 4) : AdjoinRoot f9 := AdjoinRoot.mk f9 (d9BasePoly i)
theorem d9SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 4)), d9BasePoly i) = d9V01 := by
        simp [d9BasePoly] <;> rw [d9Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 4)), d9BasePoly i) = d9V02 := by
        simp [d9BasePoly] <;> rw [d9Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 4)), d9BasePoly i) = d9V03 := by
        simp [d9BasePoly] <;> rw [d9Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({2} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 4)), d9BasePoly i) = d9V04 := by
        simp [d9BasePoly] <;> rw [d9Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,2} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 4)), d9BasePoly i) = d9V05 := by
        simp [d9BasePoly] <;> rw [d9Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,2} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 4)), d9BasePoly i) = d9V06 := by
        simp [d9BasePoly] <;> rw [d9Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,2} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), d9BasePoly i) = d9V07 := by
        simp [d9BasePoly] <;> rw [d9Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 4)), d9BasePoly i) = d9V08 := by
        simp [d9BasePoly] <;> rw [d9Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 4)), d9BasePoly i) = d9V09 := by
        simp [d9BasePoly] <;> rw [d9Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 4)), d9BasePoly i) = d9V10 := by
        simp [d9BasePoly] <;> rw [d9Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), d9BasePoly i) = d9V11 := by
        simp [d9BasePoly] <;> rw [d9Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({2,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 4)), d9BasePoly i) = d9V12 := by
        simp [d9BasePoly] <;> rw [d9Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,2,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), d9BasePoly i) = d9V13 := by
        simp [d9BasePoly] <;> rw [d9Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,2,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), d9BasePoly i) = d9V14 := by
        simp [d9BasePoly] <;> rw [d9Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem d9SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), d9Base i) = AdjoinRoot.mk f9 d9V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), d9BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 d9V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), d9BasePoly i) = d9V15 := by
        simp [d9BasePoly] <;> rw [d9Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly

#print axioms d9SubsetSum01
#print axioms d9SubsetSum15
