import Carlet.N17FourComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
def e17BasePoly : Fin 4 → P17
| 0 => e17V01
| 1 => e17V02
| 2 => e17V04
| 3 => e17V08
def e17Base (i : Fin 4) : AdjoinRoot f17 := AdjoinRoot.mk f17 (e17BasePoly i)
theorem e17SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 4)), e17BasePoly i) = e17V01 := by
        simp [e17BasePoly] <;> rw [e17Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 4)), e17BasePoly i) = e17V02 := by
        simp [e17BasePoly] <;> rw [e17Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 4)), e17BasePoly i) = e17V03 := by
        simp [e17BasePoly] <;> rw [e17Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({2} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 4)), e17BasePoly i) = e17V04 := by
        simp [e17BasePoly] <;> rw [e17Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,2} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 4)), e17BasePoly i) = e17V05 := by
        simp [e17BasePoly] <;> rw [e17Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,2} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 4)), e17BasePoly i) = e17V06 := by
        simp [e17BasePoly] <;> rw [e17Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e17BasePoly i) = e17V07 := by
        simp [e17BasePoly] <;> rw [e17Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 4)), e17BasePoly i) = e17V08 := by
        simp [e17BasePoly] <;> rw [e17Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 4)), e17BasePoly i) = e17V09 := by
        simp [e17BasePoly] <;> rw [e17Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 4)), e17BasePoly i) = e17V10 := by
        simp [e17BasePoly] <;> rw [e17Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e17BasePoly i) = e17V11 := by
        simp [e17BasePoly] <;> rw [e17Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({2,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 4)), e17BasePoly i) = e17V12 := by
        simp [e17BasePoly] <;> rw [e17Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e17BasePoly i) = e17V13 := by
        simp [e17BasePoly] <;> rw [e17Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e17BasePoly i) = e17V14 := by
        simp [e17BasePoly] <;> rw [e17Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem e17SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e17Base i) = AdjoinRoot.mk f17 e17V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 e17V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e17BasePoly i) = e17V15 := by
        simp [e17BasePoly] <;> rw [e17Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly

#print axioms e17SubsetSum01
#print axioms e17SubsetSum15
