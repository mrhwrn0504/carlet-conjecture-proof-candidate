import Carlet.N11ComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
def certBasePoly : Fin 5 → P
| 0 => certV01
| 1 => certV02
| 2 => certV04
| 3 => certV08
| 4 => certV16
def certBase (i : Fin 5) : AdjoinRoot f := AdjoinRoot.mk f (certBasePoly i)
theorem certSubsetSum01 : (∑ i ∈ ({0} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV01 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 5)), certBasePoly i) = certV01 := by
        simp [certBasePoly] <;> rw [certCombo01] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum02 : (∑ i ∈ ({1} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV02 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV02 := by
      have hpoly : (∑ i ∈ ({1} : Finset (Fin 5)), certBasePoly i) = certV02 := by
        simp [certBasePoly] <;> rw [certCombo02] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV03 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 5)), certBasePoly i) = certV03 := by
        simp [certBasePoly] <;> rw [certCombo03] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum04 : (∑ i ∈ ({2} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV04 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({2} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV04 := by
      have hpoly : (∑ i ∈ ({2} : Finset (Fin 5)), certBasePoly i) = certV04 := by
        simp [certBasePoly] <;> rw [certCombo04] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV05 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,2} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV05 := by
      have hpoly : (∑ i ∈ ({0,2} : Finset (Fin 5)), certBasePoly i) = certV05 := by
        simp [certBasePoly] <;> rw [certCombo05] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV06 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,2} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV06 := by
      have hpoly : (∑ i ∈ ({1,2} : Finset (Fin 5)), certBasePoly i) = certV06 := by
        simp [certBasePoly] <;> rw [certCombo06] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV07 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,2} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV07 := by
      have hpoly : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), certBasePoly i) = certV07 := by
        simp [certBasePoly] <;> rw [certCombo07] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum08 : (∑ i ∈ ({3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV08 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV08 := by
      have hpoly : (∑ i ∈ ({3} : Finset (Fin 5)), certBasePoly i) = certV08 := by
        simp [certBasePoly] <;> rw [certCombo08] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV09 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV09 := by
      have hpoly : (∑ i ∈ ({0,3} : Finset (Fin 5)), certBasePoly i) = certV09 := by
        simp [certBasePoly] <;> rw [certCombo09] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV10 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV10 := by
      have hpoly : (∑ i ∈ ({1,3} : Finset (Fin 5)), certBasePoly i) = certV10 := by
        simp [certBasePoly] <;> rw [certCombo10] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV11 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV11 := by
      have hpoly : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), certBasePoly i) = certV11 := by
        simp [certBasePoly] <;> rw [certCombo11] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV12 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({2,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV12 := by
      have hpoly : (∑ i ∈ ({2,3} : Finset (Fin 5)), certBasePoly i) = certV12 := by
        simp [certBasePoly] <;> rw [certCombo12] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV13 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,2,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV13 := by
      have hpoly : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), certBasePoly i) = certV13 := by
        simp [certBasePoly] <;> rw [certCombo13] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV14 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,2,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV14 := by
      have hpoly : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), certBasePoly i) = certV14 := by
        simp [certBasePoly] <;> rw [certCombo14] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV15 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV15 := by
      have hpoly : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), certBasePoly i) = certV15 := by
        simp [certBasePoly] <;> rw [certCombo15] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum16 : (∑ i ∈ ({4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV16 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV16 := by
      have hpoly : (∑ i ∈ ({4} : Finset (Fin 5)), certBasePoly i) = certV16 := by
        simp [certBasePoly] <;> rw [certCombo16] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum17 : (∑ i ∈ ({0,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV17 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV17 := by
      have hpoly : (∑ i ∈ ({0,4} : Finset (Fin 5)), certBasePoly i) = certV17 := by
        simp [certBasePoly] <;> rw [certCombo17] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum18 : (∑ i ∈ ({1,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV18 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV18 := by
      have hpoly : (∑ i ∈ ({1,4} : Finset (Fin 5)), certBasePoly i) = certV18 := by
        simp [certBasePoly] <;> rw [certCombo18] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum19 : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV19 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV19 := by
      have hpoly : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), certBasePoly i) = certV19 := by
        simp [certBasePoly] <;> rw [certCombo19] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum20 : (∑ i ∈ ({2,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV20 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({2,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV20 := by
      have hpoly : (∑ i ∈ ({2,4} : Finset (Fin 5)), certBasePoly i) = certV20 := by
        simp [certBasePoly] <;> rw [certCombo20] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum21 : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV21 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,2,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV21 := by
      have hpoly : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), certBasePoly i) = certV21 := by
        simp [certBasePoly] <;> rw [certCombo21] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum22 : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV22 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,2,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV22 := by
      have hpoly : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), certBasePoly i) = certV22 := by
        simp [certBasePoly] <;> rw [certCombo22] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum23 : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV23 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV23 := by
      have hpoly : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), certBasePoly i) = certV23 := by
        simp [certBasePoly] <;> rw [certCombo23] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum24 : (∑ i ∈ ({3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV24 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV24 := by
      have hpoly : (∑ i ∈ ({3,4} : Finset (Fin 5)), certBasePoly i) = certV24 := by
        simp [certBasePoly] <;> rw [certCombo24] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum25 : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV25 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV25 := by
      have hpoly : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), certBasePoly i) = certV25 := by
        simp [certBasePoly] <;> rw [certCombo25] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum26 : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV26 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV26 := by
      have hpoly : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), certBasePoly i) = certV26 := by
        simp [certBasePoly] <;> rw [certCombo26] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum27 : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV27 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV27 := by
      have hpoly : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), certBasePoly i) = certV27 := by
        simp [certBasePoly] <;> rw [certCombo27] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum28 : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV28 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({2,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV28 := by
      have hpoly : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), certBasePoly i) = certV28 := by
        simp [certBasePoly] <;> rw [certCombo28] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum29 : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV29 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV29 := by
      have hpoly : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), certBasePoly i) = certV29 := by
        simp [certBasePoly] <;> rw [certCombo29] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum30 : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV30 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV30 := by
      have hpoly : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), certBasePoly i) = certV30 := by
        simp [certBasePoly] <;> rw [certCombo30] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
theorem certSubsetSum31 : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), certBase i) = AdjoinRoot.mk f certV31 := by
  classical
  calc
    _ = AdjoinRoot.mk f (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), certBasePoly i) := (map_sum (AdjoinRoot.mk f) _ _).symm
    _ = AdjoinRoot.mk f certV31 := by
      have hpoly : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), certBasePoly i) = certV31 := by
        simp [certBasePoly] <;> rw [certCombo31] <;> ac_rfl
      exact congrArg (AdjoinRoot.mk f) hpoly
#print axioms certSubsetSum01
#print axioms certSubsetSum31





