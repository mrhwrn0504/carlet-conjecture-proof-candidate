import Carlet.Theta5SubstitutionDegreeProbe
import Carlet.Theta5HyperplaneWitnessProbe
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

abbrev Theta5Other (p : Fin 5) := {i : Fin 5 // i ≠ p}

/-- Coordinates on the binary hyperplane with nonzero pivot coefficient. -/
def theta5Chart (r : Fin 5 → ZMod 2) (p i : Fin 5) :
    MvPolynomial (Theta5Other p) K :=
  if h : i = p then
    ∑ j : Theta5Other p,
      MvPolynomial.C (algebraMap (ZMod 2) K (r j.val)) * MvPolynomial.X j
  else MvPolynomial.X ⟨i, h⟩

theorem theta5Chart_degree_le (r : Fin 5 → ZMod 2) (p i : Fin 5) :
    (theta5Chart (K := K) r p i).totalDegree ≤ 1 := by
  classical
  unfold theta5Chart
  split_ifs
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    calc
      _ ≤ (MvPolynomial.C (algebraMap (ZMod 2) K (r j.val)) :
          MvPolynomial (Theta5Other p) K).totalDegree +
          (MvPolynomial.X j : MvPolynomial (Theta5Other p) K).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simp
  · simp

theorem theta5Chart_covers (r : Fin 5 → ZMod 2) (p : Fin 5) (hrp : r p ≠ 0)
    (x : Fin 5 → K)
    (hx : (∑ i : Fin 5, algebraMap (ZMod 2) K (r i) * x i) = 0) :
    ∃ y : Theta5Other p → K, ∀ i,
      MvPolynomial.eval y (theta5Chart (K := K) r p i) = x i := by
  classical
  have hrp1 : r p = 1 := by
    generalize hval : r p = a
    fin_cases a
    · exact False.elim (hrp hval)
    · rfl
  have hsum : (∑ j : Theta5Other p, algebraMap (ZMod 2) K (r j.val) * x j.val) =
      ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase p,
        algebraMap (ZMod 2) K (r j) * x j := by
    have hset : (Finset.univ : Finset (Fin 5)).filter (fun j => j ≠ p) =
        (Finset.univ : Finset (Fin 5)).erase p := by
      ext j
      simp
    rw [← hset]
    simpa [Theta5Other] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin 5)))
        (p := fun j => j ≠ p) (fun j => algebraMap (ZMod 2) K (r j) * x j))
  have hlast := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
    (fun j => algebraMap (ZMod 2) K (r j) * x j) (Finset.mem_univ p)
  rw [← hsum, hx, hrp1] at hlast
  simp only [map_one, one_mul] at hlast
  have hp : x p = ∑ j : Theta5Other p, algebraMap (ZMod 2) K (r j.val) * x j.val := by
    simpa only [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp hlast).symm
  refine ⟨fun j => x j.val, ?_⟩
  intro i
  by_cases hi : i = p
  · subst i
    simp [theta5Chart, hp]
  · simp [theta5Chart, hi]

def theta5ChartPullback (r : Fin 5 → ZMod 2) (p : Fin 5) :
    MvPolynomial (Theta5Other p) K :=
  theta5SubstHom (theta5Chart (K := K) r p) theta5

theorem theta5ChartPullback_eval (r : Fin 5 → ZMod 2) (p : Fin 5)
    (y : Theta5Other p → K) :
    MvPolynomial.eval y (theta5ChartPullback (K := K) r p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval y (theta5Chart (K := K) r p i))
        (theta5.map (algebraMap (ZMod 2) K)) := by
  have hcomp : (MvPolynomial.eval y).comp
      ((MvPolynomial.C : K →+* MvPolynomial (Theta5Other p) K).comp
        (algebraMap (ZMod 2) K)) = algebraMap (ZMod 2) K := by
    ext a
    simp
  simp [theta5ChartPullback, theta5SubstHom, MvPolynomial.eval_eval₂,
    MvPolynomial.eval_map, hcomp]

theorem theta5ChartPullback_degree_le (r : Fin 5 → ZMod 2) (p : Fin 5) :
    (theta5ChartPullback (K := K) r p).totalDegree ≤ 16 :=
  theta5_linear_substitution_totalDegree_le _ (theta5Chart_degree_le r p)

theorem theta5ChartPullback_ne_zero (r : Fin 5 → ZMod 2) (p : Fin 5)
    (hrp : r p ≠ 0) : theta5ChartPullback (K := K) r p ≠ 0 := by
  obtain ⟨x, hx, htheta⟩ := theta5_field_hyperplane_has_value_one (K := K) r
  obtain ⟨y, hy⟩ := theta5Chart_covers r p hrp x hx
  intro hzero
  have heval := congrArg (MvPolynomial.eval y) hzero
  rw [map_zero, theta5ChartPullback_eval] at heval
  have hcoords : (fun i => MvPolynomial.eval y (theta5Chart (K := K) r p i)) = x :=
    funext hy
  rw [hcoords, htheta] at heval
  exact one_ne_zero heval

#print axioms theta5Chart_covers
#print axioms theta5ChartPullback_degree_le
#print axioms theta5ChartPullback_ne_zero
end Carlet
