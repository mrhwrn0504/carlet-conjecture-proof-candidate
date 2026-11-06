import Carlet.N13K4InverseSumProbe
import Carlet.N13K5SubfieldProbe
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic
open Polynomial Carlet
noncomputable section
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩

namespace Carlet

/-- The explicit four-dimensional certificate in degree 13 transports to
    every finite extension whose degree is divisible by 13. -/
theorem hasZeroSumSubspace_four_of_13_dvd_card {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hdiv : 13 ∣ n) : HasZeroSumSubspace K 4 := by
  classical
  let L := AdjoinRoot f13
  have hLcard : Fintype.card L = 2 ^ 13 := by
    simpa [L] using adjoinRoot13_card
  have hLrank : Module.finrank (ZMod 2) L = 13 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hLcard
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hLcard
  have hKrank : Module.finrank (ZMod 2) K = n := finrank_eq_of_card n hcard
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hLrank, hKrank] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom13_probe e e.injective 4
    N13K4.hasZeroSumSubspace_adjoinRoot

#print axioms hasZeroSumSubspace_four_of_13_dvd_card
end Carlet
