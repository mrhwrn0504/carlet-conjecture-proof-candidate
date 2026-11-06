import Carlet.N13K4GeneratedData
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
namespace N13K4
def base (i : Fin 4) : AdjoinRoot f13 := AdjoinRoot.mk f13 (Carlet.n13K4BasePoly i)

theorem subsetSum01 :
    (∑ i ∈ ({0} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P01 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P01 := by
      have hpoly : (∑ i ∈ ({0} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P01 := by
        norm_num [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4P01]
      exact congrArg (AdjoinRoot.mk f13) hpoly

theorem subsetSum03 :
    (∑ i ∈ ({0,1} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P03 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P03 := by
      have hpoly : (∑ i ∈ ({0,1} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P03 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4P03]
        ring_nf
      exact congrArg (AdjoinRoot.mk f13) hpoly

end N13K4
end
