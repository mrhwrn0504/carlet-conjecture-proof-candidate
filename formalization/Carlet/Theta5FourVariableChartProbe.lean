import Carlet.Theta5HyperplaneChartProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

theorem theta5Other_card (p : Fin 5) : Fintype.card (Theta5Other p) = 4 := by
  classical
  have hs : Fintype.card {i : Fin 5 // i = p} = 1 := by
    let : Unique {i : Fin 5 // i = p} := ⟨⟨p, rfl⟩, fun x => Subtype.ext x.property⟩
    exact Fintype.card_unique
  change Fintype.card {i : Fin 5 // ¬ i = p} = 4
  rw [Fintype.card_subtype_compl, hs]
  decide

def theta5OtherEquiv (p : Fin 5) : Theta5Other p ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (theta5Other_card p)

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

def theta5Chart4Pullback (r : Fin 5 → ZMod 2) (p : Fin 5) : MvPolynomial (Fin 4) K :=
  MvPolynomial.rename (theta5OtherEquiv p) (theta5ChartPullback (K := K) r p)

theorem theta5Chart4Pullback_eval (r : Fin 5 → ZMod 2) (p : Fin 5)
    (y : Fin 4 → K) :
    MvPolynomial.eval y (theta5Chart4Pullback (K := K) r p) =
      MvPolynomial.eval (y ∘ theta5OtherEquiv p) (theta5ChartPullback (K := K) r p) := by
  exact MvPolynomial.eval_rename (theta5OtherEquiv p) y _

theorem theta5Chart4Pullback_degree_le (r : Fin 5 → ZMod 2) (p : Fin 5) :
    (theta5Chart4Pullback (K := K) r p).totalDegree ≤ 16 :=
  (MvPolynomial.totalDegree_rename_le (theta5OtherEquiv p) _).trans
    (theta5ChartPullback_degree_le r p)

theorem theta5Chart4Pullback_ne_zero (r : Fin 5 → ZMod 2) (p : Fin 5)
    (hrp : r p ≠ 0) : theta5Chart4Pullback (K := K) r p ≠ 0 := by
  intro hzero
  apply theta5ChartPullback_ne_zero (K := K) r p hrp
  apply MvPolynomial.rename_injective (theta5OtherEquiv p) (theta5OtherEquiv p).injective
  simpa [theta5Chart4Pullback] using hzero

#print axioms theta5Other_card
#print axioms theta5Chart4Pullback_eval
#print axioms theta5Chart4Pullback_degree_le
#print axioms theta5Chart4Pullback_ne_zero
end Carlet
