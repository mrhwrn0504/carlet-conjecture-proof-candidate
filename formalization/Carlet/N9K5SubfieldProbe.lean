import Carlet.N9K5CompleteProbe
import Carlet.N11K5SubfieldProbe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial Carlet
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
namespace Carlet
theorem hasZeroSumSubspace_five_of_9_dvd {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hdiv : 9 ∣ n) : HasZeroSumSubspace K 5 := by
  classical
  let L := AdjoinRoot f9
  have hr : Module.finrank (ZMod 2) L = 9 := by
    have hc : Fintype.card L = 2 ^ 9 := by simpa [L] using adjoinRoot9_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hc
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hc
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, hn] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 5 hasZeroSumSubspace_512_five_probe
end Carlet
#print axioms Carlet.hasZeroSumSubspace_five_of_9_dvd
