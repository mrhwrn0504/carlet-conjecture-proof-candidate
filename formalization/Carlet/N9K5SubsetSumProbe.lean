import Carlet.N9K5ComboProbe
import Carlet.N9K5InverseAdjoinProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
def n9K5Base (i : Fin 5) : AdjoinRoot f9 := AdjoinRoot.mk f9 (n9K5BasePoly i)
def n9K5SubsetSum (s : Finset (Fin 5)) : AdjoinRoot f9 := ∑ i ∈ s, n9K5Base i
theorem n9K5SubsetSum_empty : n9K5SubsetSum ∅ = 0 := by simp [n9K5SubsetSum]
theorem n9K5SubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V01 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V01 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V02 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V02 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V03 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V04 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({2} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V04 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V05 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,2} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V05 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V06 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,2} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V06 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V07 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,2} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V07 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V08 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V08 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V09 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V09 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V10 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V10 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V11 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V11 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V12 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({2,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V12 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V13 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,2,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V13 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V14 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,2,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V14 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V15 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V15 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum16 : (∑ i ∈ ({4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V16 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V16 := by
      have hpoly : (∑ i ∈ ({4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V16 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo16] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum17 : (∑ i ∈ ({0,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V17 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V17 := by
      have hpoly : (∑ i ∈ ({0,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V17 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo17] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum18 : (∑ i ∈ ({1,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V18 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V18 := by
      have hpoly : (∑ i ∈ ({1,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V18 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo18] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum19 : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V19 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V19 := by
      have hpoly : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V19 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo19] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum20 : (∑ i ∈ ({2,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V20 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({2,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V20 := by
      have hpoly : (∑ i ∈ ({2,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V20 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo20] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum21 : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V21 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,2,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V21 := by
      have hpoly : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V21 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo21] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum22 : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V22 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,2,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V22 := by
      have hpoly : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V22 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo22] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum23 : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V23 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V23 := by
      have hpoly : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V23 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo23] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum24 : (∑ i ∈ ({3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V24 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V24 := by
      have hpoly : (∑ i ∈ ({3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V24 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo24] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum25 : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V25 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V25 := by
      have hpoly : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V25 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo25] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum26 : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V26 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V26 := by
      have hpoly : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V26 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo26] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum27 : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V27 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V27 := by
      have hpoly : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V27 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo27] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum28 : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V28 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({2,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V28 := by
      have hpoly : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V28 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo28] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum29 : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V29 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V29 := by
      have hpoly : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V29 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo29] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum30 : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V30 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V30 := by
      have hpoly : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V30 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo30] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
theorem n9K5SubsetSum31 : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), n9K5Base i) = AdjoinRoot.mk f9 n9K5V31 := by
  classical
  calc
    _ = AdjoinRoot.mk f9 (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), n9K5BasePoly i) := (map_sum (AdjoinRoot.mk f9) _ _).symm
    _ = AdjoinRoot.mk f9 n9K5V31 := by
      have hpoly : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), n9K5BasePoly i) = n9K5V31 := by
        simp [n9K5BasePoly] <;> rw [n9K5Combo31] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f9) hpoly
#print axioms n9K5SubsetSum01
#print axioms n9K5SubsetSum31


