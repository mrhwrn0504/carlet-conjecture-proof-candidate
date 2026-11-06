import Carlet.N17ComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
def c17BasePoly : Fin 5 → P17
| 0 => c17V01
| 1 => c17V02
| 2 => c17V04
| 3 => c17V08
| 4 => c17V16
def c17Base (i : Fin 5) : AdjoinRoot f17 := AdjoinRoot.mk f17 (c17BasePoly i)
theorem c17SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 5)), c17BasePoly i) = c17V01 := by
        simp [c17BasePoly] <;> rw [c17Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 5)), c17BasePoly i) = c17V02 := by
        simp [c17BasePoly] <;> rw [c17Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 5)), c17BasePoly i) = c17V03 := by
        simp [c17BasePoly] <;> rw [c17Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({2} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 5)), c17BasePoly i) = c17V04 := by
        simp [c17BasePoly] <;> rw [c17Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,2} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 5)), c17BasePoly i) = c17V05 := by
        simp [c17BasePoly] <;> rw [c17Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,2} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 5)), c17BasePoly i) = c17V06 := by
        simp [c17BasePoly] <;> rw [c17Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,2} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), c17BasePoly i) = c17V07 := by
        simp [c17BasePoly] <;> rw [c17Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 5)), c17BasePoly i) = c17V08 := by
        simp [c17BasePoly] <;> rw [c17Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 5)), c17BasePoly i) = c17V09 := by
        simp [c17BasePoly] <;> rw [c17Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 5)), c17BasePoly i) = c17V10 := by
        simp [c17BasePoly] <;> rw [c17Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), c17BasePoly i) = c17V11 := by
        simp [c17BasePoly] <;> rw [c17Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({2,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 5)), c17BasePoly i) = c17V12 := by
        simp [c17BasePoly] <;> rw [c17Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,2,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), c17BasePoly i) = c17V13 := by
        simp [c17BasePoly] <;> rw [c17Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,2,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), c17BasePoly i) = c17V14 := by
        simp [c17BasePoly] <;> rw [c17Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), c17BasePoly i) = c17V15 := by
        simp [c17BasePoly] <;> rw [c17Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum16 : (∑ i ∈ ({4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V16 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V16 := by
      have hpoly : (∑ i ∈ ({4} : Finset (Fin 5)), c17BasePoly i) = c17V16 := by
        simp [c17BasePoly] <;> rw [c17Combo16] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum17 : (∑ i ∈ ({0,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V17 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V17 := by
      have hpoly : (∑ i ∈ ({0,4} : Finset (Fin 5)), c17BasePoly i) = c17V17 := by
        simp [c17BasePoly] <;> rw [c17Combo17] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum18 : (∑ i ∈ ({1,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V18 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V18 := by
      have hpoly : (∑ i ∈ ({1,4} : Finset (Fin 5)), c17BasePoly i) = c17V18 := by
        simp [c17BasePoly] <;> rw [c17Combo18] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum19 : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V19 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V19 := by
      have hpoly : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), c17BasePoly i) = c17V19 := by
        simp [c17BasePoly] <;> rw [c17Combo19] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum20 : (∑ i ∈ ({2,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V20 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({2,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V20 := by
      have hpoly : (∑ i ∈ ({2,4} : Finset (Fin 5)), c17BasePoly i) = c17V20 := by
        simp [c17BasePoly] <;> rw [c17Combo20] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum21 : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V21 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,2,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V21 := by
      have hpoly : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), c17BasePoly i) = c17V21 := by
        simp [c17BasePoly] <;> rw [c17Combo21] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum22 : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V22 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,2,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V22 := by
      have hpoly : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), c17BasePoly i) = c17V22 := by
        simp [c17BasePoly] <;> rw [c17Combo22] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum23 : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V23 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V23 := by
      have hpoly : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), c17BasePoly i) = c17V23 := by
        simp [c17BasePoly] <;> rw [c17Combo23] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum24 : (∑ i ∈ ({3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V24 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V24 := by
      have hpoly : (∑ i ∈ ({3,4} : Finset (Fin 5)), c17BasePoly i) = c17V24 := by
        simp [c17BasePoly] <;> rw [c17Combo24] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum25 : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V25 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V25 := by
      have hpoly : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V25 := by
        simp [c17BasePoly] <;> rw [c17Combo25] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum26 : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V26 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V26 := by
      have hpoly : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V26 := by
        simp [c17BasePoly] <;> rw [c17Combo26] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum27 : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V27 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V27 := by
      have hpoly : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V27 := by
        simp [c17BasePoly] <;> rw [c17Combo27] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum28 : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V28 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({2,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V28 := by
      have hpoly : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V28 := by
        simp [c17BasePoly] <;> rw [c17Combo28] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum29 : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V29 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V29 := by
      have hpoly : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V29 := by
        simp [c17BasePoly] <;> rw [c17Combo29] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum30 : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V30 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V30 := by
      have hpoly : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V30 := by
        simp [c17BasePoly] <;> rw [c17Combo30] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
theorem c17SubsetSum31 : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), c17Base i) = AdjoinRoot.mk f17 c17V31 := by
  classical
  calc
    _ = AdjoinRoot.mk f17 (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), c17BasePoly i) := (map_sum (AdjoinRoot.mk f17) _ _).symm
    _ = AdjoinRoot.mk f17 c17V31 := by
      have hpoly : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), c17BasePoly i) = c17V31 := by
        simp [c17BasePoly] <;> rw [c17Combo31] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f17) hpoly
#print axioms c17SubsetSum01
#print axioms c17SubsetSum31





