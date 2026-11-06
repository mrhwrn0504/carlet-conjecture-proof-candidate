import Carlet.N19FourComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
def e19BasePoly : Fin 4 → P19
| 0 => e19V01
| 1 => e19V02
| 2 => e19V04
| 3 => e19V08
def e19Base (i : Fin 4) : AdjoinRoot f19 := AdjoinRoot.mk f19 (e19BasePoly i)
theorem e19SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 4)), e19BasePoly i) = e19V01 := by
        simp [e19BasePoly] <;> rw [e19Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 4)), e19BasePoly i) = e19V02 := by
        simp [e19BasePoly] <;> rw [e19Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 4)), e19BasePoly i) = e19V03 := by
        simp [e19BasePoly] <;> rw [e19Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({2} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 4)), e19BasePoly i) = e19V04 := by
        simp [e19BasePoly] <;> rw [e19Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,2} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 4)), e19BasePoly i) = e19V05 := by
        simp [e19BasePoly] <;> rw [e19Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,2} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 4)), e19BasePoly i) = e19V06 := by
        simp [e19BasePoly] <;> rw [e19Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), e19BasePoly i) = e19V07 := by
        simp [e19BasePoly] <;> rw [e19Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 4)), e19BasePoly i) = e19V08 := by
        simp [e19BasePoly] <;> rw [e19Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 4)), e19BasePoly i) = e19V09 := by
        simp [e19BasePoly] <;> rw [e19Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 4)), e19BasePoly i) = e19V10 := by
        simp [e19BasePoly] <;> rw [e19Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), e19BasePoly i) = e19V11 := by
        simp [e19BasePoly] <;> rw [e19Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({2,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 4)), e19BasePoly i) = e19V12 := by
        simp [e19BasePoly] <;> rw [e19Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), e19BasePoly i) = e19V13 := by
        simp [e19BasePoly] <;> rw [e19Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), e19BasePoly i) = e19V14 := by
        simp [e19BasePoly] <;> rw [e19Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem e19SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e19Base i) = AdjoinRoot.mk f19 e19V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 e19V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), e19BasePoly i) = e19V15 := by
        simp [e19BasePoly] <;> rw [e19Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly

#print axioms e19SubsetSum01
#print axioms e19SubsetSum15
