import Carlet.N19ComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
def c19BasePoly : Fin 5 → P17
| 0 => c19V01
| 1 => c19V02
| 2 => c19V04
| 3 => c19V08
| 4 => c19V16
def c19Base (i : Fin 5) : AdjoinRoot f19 := AdjoinRoot.mk f19 (c19BasePoly i)
theorem c19SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 5)), c19BasePoly i) = c19V01 := by
        simp [c19BasePoly] <;> rw [c19Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 5)), c19BasePoly i) = c19V02 := by
        simp [c19BasePoly] <;> rw [c19Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 5)), c19BasePoly i) = c19V03 := by
        simp [c19BasePoly] <;> rw [c19Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({2} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 5)), c19BasePoly i) = c19V04 := by
        simp [c19BasePoly] <;> rw [c19Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,2} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 5)), c19BasePoly i) = c19V05 := by
        simp [c19BasePoly] <;> rw [c19Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,2} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 5)), c19BasePoly i) = c19V06 := by
        simp [c19BasePoly] <;> rw [c19Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,2} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), c19BasePoly i) = c19V07 := by
        simp [c19BasePoly] <;> rw [c19Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 5)), c19BasePoly i) = c19V08 := by
        simp [c19BasePoly] <;> rw [c19Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 5)), c19BasePoly i) = c19V09 := by
        simp [c19BasePoly] <;> rw [c19Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 5)), c19BasePoly i) = c19V10 := by
        simp [c19BasePoly] <;> rw [c19Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), c19BasePoly i) = c19V11 := by
        simp [c19BasePoly] <;> rw [c19Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({2,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 5)), c19BasePoly i) = c19V12 := by
        simp [c19BasePoly] <;> rw [c19Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,2,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), c19BasePoly i) = c19V13 := by
        simp [c19BasePoly] <;> rw [c19Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,2,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), c19BasePoly i) = c19V14 := by
        simp [c19BasePoly] <;> rw [c19Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), c19BasePoly i) = c19V15 := by
        simp [c19BasePoly] <;> rw [c19Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum16 : (∑ i ∈ ({4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V16 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V16 := by
      have hpoly : (∑ i ∈ ({4} : Finset (Fin 5)), c19BasePoly i) = c19V16 := by
        simp [c19BasePoly] <;> rw [c19Combo16] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum17 : (∑ i ∈ ({0,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V17 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V17 := by
      have hpoly : (∑ i ∈ ({0,4} : Finset (Fin 5)), c19BasePoly i) = c19V17 := by
        simp [c19BasePoly] <;> rw [c19Combo17] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum18 : (∑ i ∈ ({1,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V18 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V18 := by
      have hpoly : (∑ i ∈ ({1,4} : Finset (Fin 5)), c19BasePoly i) = c19V18 := by
        simp [c19BasePoly] <;> rw [c19Combo18] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum19 : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V19 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V19 := by
      have hpoly : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), c19BasePoly i) = c19V19 := by
        simp [c19BasePoly] <;> rw [c19Combo19] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum20 : (∑ i ∈ ({2,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V20 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({2,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V20 := by
      have hpoly : (∑ i ∈ ({2,4} : Finset (Fin 5)), c19BasePoly i) = c19V20 := by
        simp [c19BasePoly] <;> rw [c19Combo20] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum21 : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V21 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,2,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V21 := by
      have hpoly : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), c19BasePoly i) = c19V21 := by
        simp [c19BasePoly] <;> rw [c19Combo21] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum22 : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V22 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,2,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V22 := by
      have hpoly : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), c19BasePoly i) = c19V22 := by
        simp [c19BasePoly] <;> rw [c19Combo22] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum23 : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V23 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V23 := by
      have hpoly : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), c19BasePoly i) = c19V23 := by
        simp [c19BasePoly] <;> rw [c19Combo23] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum24 : (∑ i ∈ ({3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V24 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V24 := by
      have hpoly : (∑ i ∈ ({3,4} : Finset (Fin 5)), c19BasePoly i) = c19V24 := by
        simp [c19BasePoly] <;> rw [c19Combo24] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum25 : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V25 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V25 := by
      have hpoly : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V25 := by
        simp [c19BasePoly] <;> rw [c19Combo25] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum26 : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V26 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V26 := by
      have hpoly : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V26 := by
        simp [c19BasePoly] <;> rw [c19Combo26] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum27 : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V27 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V27 := by
      have hpoly : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V27 := by
        simp [c19BasePoly] <;> rw [c19Combo27] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum28 : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V28 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({2,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V28 := by
      have hpoly : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V28 := by
        simp [c19BasePoly] <;> rw [c19Combo28] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum29 : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V29 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V29 := by
      have hpoly : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V29 := by
        simp [c19BasePoly] <;> rw [c19Combo29] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum30 : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V30 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V30 := by
      have hpoly : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V30 := by
        simp [c19BasePoly] <;> rw [c19Combo30] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
theorem c19SubsetSum31 : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), c19Base i) = AdjoinRoot.mk f19 c19V31 := by
  classical
  calc
    _ = AdjoinRoot.mk f19 (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), c19BasePoly i) := (map_sum (AdjoinRoot.mk f19) _ _).symm
    _ = AdjoinRoot.mk f19 c19V31 := by
      have hpoly : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), c19BasePoly i) = c19V31 := by
        simp [c19BasePoly] <;> rw [c19Combo31] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f19) hpoly
#print axioms c19SubsetSum01
#print axioms c19SubsetSum31





