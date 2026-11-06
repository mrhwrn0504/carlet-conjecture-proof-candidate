import Carlet.N11FourComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
def e11BasePoly : Fin 4 → P17
| 0 => e11V01
| 1 => e11V02
| 2 => e11V04
| 3 => e11V08
def e11Base (i : Fin 4) : AdjoinRoot f := AdjoinRoot.mk f (e11BasePoly i)
theorem e11SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 4)), e11BasePoly i) = e11V01 := by
        simp [e11BasePoly] <;> rw [e11Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 4)), e11BasePoly i) = e11V02 := by
        simp [e11BasePoly] <;> rw [e11Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 4)), e11BasePoly i) = e11V03 := by
        simp [e11BasePoly] <;> rw [e11Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({2} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 4)), e11BasePoly i) = e11V04 := by
        simp [e11BasePoly] <;> rw [e11Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,2} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 4)), e11BasePoly i) = e11V05 := by
        simp [e11BasePoly] <;> rw [e11Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,2} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 4)), e11BasePoly i) = e11V06 := by
        simp [e11BasePoly] <;> rw [e11Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e11BasePoly i) = e11V07 := by
        simp [e11BasePoly] <;> rw [e11Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 4)), e11BasePoly i) = e11V08 := by
        simp [e11BasePoly] <;> rw [e11Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 4)), e11BasePoly i) = e11V09 := by
        simp [e11BasePoly] <;> rw [e11Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 4)), e11BasePoly i) = e11V10 := by
        simp [e11BasePoly] <;> rw [e11Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e11BasePoly i) = e11V11 := by
        simp [e11BasePoly] <;> rw [e11Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({2,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 4)), e11BasePoly i) = e11V12 := by
        simp [e11BasePoly] <;> rw [e11Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e11BasePoly i) = e11V13 := by
        simp [e11BasePoly] <;> rw [e11Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e11BasePoly i) = e11V14 := by
        simp [e11BasePoly] <;> rw [e11Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem e11SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e11Base i) = AdjoinRoot.mk f e11V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e11BasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f e11V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e11BasePoly i) = e11V15 := by
        simp [e11BasePoly] <;> rw [e11Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly

#print axioms e11SubsetSum01
#print axioms e11SubsetSum15
