import Carlet.N13ComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
def cert13BasePoly : Fin 5 → P13
| 0 => cert13V01
| 1 => cert13V02
| 2 => cert13V04
| 3 => cert13V08
| 4 => cert13V16
def cert13Base (i : Fin 5) : AdjoinRoot f13 := AdjoinRoot.mk f13 (cert13BasePoly i)
theorem cert13SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 5)), cert13BasePoly i) = cert13V01 := by
        simp [cert13BasePoly] <;> rw [cert13Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 5)), cert13BasePoly i) = cert13V02 := by
        simp [cert13BasePoly] <;> rw [cert13Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 5)), cert13BasePoly i) = cert13V03 := by
        simp [cert13BasePoly] <;> rw [cert13Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({2} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 5)), cert13BasePoly i) = cert13V04 := by
        simp [cert13BasePoly] <;> rw [cert13Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,2} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 5)), cert13BasePoly i) = cert13V05 := by
        simp [cert13BasePoly] <;> rw [cert13Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,2} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 5)), cert13BasePoly i) = cert13V06 := by
        simp [cert13BasePoly] <;> rw [cert13Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,2} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), cert13BasePoly i) = cert13V07 := by
        simp [cert13BasePoly] <;> rw [cert13Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 5)), cert13BasePoly i) = cert13V08 := by
        simp [cert13BasePoly] <;> rw [cert13Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V09 := by
        simp [cert13BasePoly] <;> rw [cert13Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V10 := by
        simp [cert13BasePoly] <;> rw [cert13Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V11 := by
        simp [cert13BasePoly] <;> rw [cert13Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({2,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V12 := by
        simp [cert13BasePoly] <;> rw [cert13Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,2,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V13 := by
        simp [cert13BasePoly] <;> rw [cert13Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,2,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V14 := by
        simp [cert13BasePoly] <;> rw [cert13Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), cert13BasePoly i) = cert13V15 := by
        simp [cert13BasePoly] <;> rw [cert13Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum16 : (∑ i ∈ ({4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V16 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V16 := by
      have hpoly : (∑ i ∈ ({4} : Finset (Fin 5)), cert13BasePoly i) = cert13V16 := by
        simp [cert13BasePoly] <;> rw [cert13Combo16] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum17 : (∑ i ∈ ({0,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V17 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V17 := by
      have hpoly : (∑ i ∈ ({0,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V17 := by
        simp [cert13BasePoly] <;> rw [cert13Combo17] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum18 : (∑ i ∈ ({1,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V18 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V18 := by
      have hpoly : (∑ i ∈ ({1,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V18 := by
        simp [cert13BasePoly] <;> rw [cert13Combo18] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum19 : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V19 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V19 := by
      have hpoly : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V19 := by
        simp [cert13BasePoly] <;> rw [cert13Combo19] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum20 : (∑ i ∈ ({2,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V20 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({2,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V20 := by
      have hpoly : (∑ i ∈ ({2,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V20 := by
        simp [cert13BasePoly] <;> rw [cert13Combo20] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum21 : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V21 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,2,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V21 := by
      have hpoly : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V21 := by
        simp [cert13BasePoly] <;> rw [cert13Combo21] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum22 : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V22 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,2,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V22 := by
      have hpoly : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V22 := by
        simp [cert13BasePoly] <;> rw [cert13Combo22] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum23 : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V23 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V23 := by
      have hpoly : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V23 := by
        simp [cert13BasePoly] <;> rw [cert13Combo23] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum24 : (∑ i ∈ ({3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V24 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V24 := by
      have hpoly : (∑ i ∈ ({3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V24 := by
        simp [cert13BasePoly] <;> rw [cert13Combo24] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum25 : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V25 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V25 := by
      have hpoly : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V25 := by
        simp [cert13BasePoly] <;> rw [cert13Combo25] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum26 : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V26 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V26 := by
      have hpoly : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V26 := by
        simp [cert13BasePoly] <;> rw [cert13Combo26] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum27 : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V27 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V27 := by
      have hpoly : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V27 := by
        simp [cert13BasePoly] <;> rw [cert13Combo27] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum28 : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V28 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({2,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V28 := by
      have hpoly : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V28 := by
        simp [cert13BasePoly] <;> rw [cert13Combo28] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum29 : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V29 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V29 := by
      have hpoly : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V29 := by
        simp [cert13BasePoly] <;> rw [cert13Combo29] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum30 : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V30 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V30 := by
      have hpoly : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V30 := by
        simp [cert13BasePoly] <;> rw [cert13Combo30] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
theorem cert13SubsetSum31 : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V31 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V31 := by
      have hpoly : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), cert13BasePoly i) = cert13V31 := by
        simp [cert13BasePoly] <;> rw [cert13Combo31] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f13) hpoly
#print axioms cert13SubsetSum01
#print axioms cert13SubsetSum31





