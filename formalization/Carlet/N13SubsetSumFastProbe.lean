import Carlet.N13ComboProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
def cert13BasePoly : Fin 5 → P13
| 0 => cert13V01
| 1 => cert13V02
| 2 => cert13V04
| 3 => cert13V08
| 4 => cert13V16
def cert13Base (i : Fin 5) : AdjoinRoot f13 := AdjoinRoot.mk f13 (cert13BasePoly i)
theorem testSubsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V03 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 cert13V03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 5)), cert13BasePoly i) = cert13V03 := by
        simp [cert13BasePoly]
        rw [cert13Combo03]
      exact congrArg (AdjoinRoot.mk f13) hpoly
#print axioms testSubsetSum03
