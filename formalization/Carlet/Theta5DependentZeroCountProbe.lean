import Carlet.Theta5FourVariableChartProbe
import Carlet.Theta5MainAssemblyProbe
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

theorem theta5_ambient_zeros_le_chart_zeros (r : Fin 5 → ZMod 2)
    (p : Fin 5) (hrp : r p ≠ 0) :
    Fintype.card {x : Fin 5 → K //
      (∑ i, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
      MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0} ≤
    Fintype.card {y : Fin 4 → K //
      MvPolynomial.eval y (theta5Chart4Pullback (K := K) r p) = 0} := by
  classical
  let A := {x : Fin 5 → K //
    (∑ i, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0}
  let B := {y : Fin 4 → K //
    MvPolynomial.eval y (theta5Chart4Pullback (K := K) r p) = 0}
  have hcover (x : A) := theta5Chart_covers r p hrp x.val x.property.1
  let choiceY : A → Theta5Other p → K := fun x => Classical.choose (hcover x)
  have hspec (x : A) (i : Fin 5) :
      MvPolynomial.eval (choiceY x) (theta5Chart (K := K) r p i) = x.val i :=
    Classical.choose_spec (hcover x) i
  let f : A → B := fun x => ⟨fun i => choiceY x ((theta5OtherEquiv p).symm i), by
    rw [theta5Chart4Pullback_eval]
    have hy : (fun i : Fin 4 => choiceY x ((theta5OtherEquiv p).symm i)) ∘
        theta5OtherEquiv p = choiceY x := by
      funext i
      simp
    rw [hy, theta5ChartPullback_eval, funext (hspec x)]
    exact x.property.2⟩
  have hinj : Function.Injective f := by
    intro x z h
    have hy : choiceY x = choiceY z := by
      funext i
      have hval := congrFun (congrArg Subtype.val h) (theta5OtherEquiv p i)
      simpa [f] using hval
    apply Subtype.ext
    funext i
    calc
      x.val i = MvPolynomial.eval (choiceY x) (theta5Chart (K := K) r p i) :=
        (hspec x i).symm
      _ = MvPolynomial.eval (choiceY z) (theta5Chart (K := K) r p i) := by rw [hy]
      _ = z.val i := hspec z i
  exact Fintype.card_le_of_injective f hinj

theorem theta5_chart_zero_count_le (r : Fin 5 → ZMod 2) (p : Fin 5)
    (hrp : r p ≠ 0) :
    Fintype.card {y : Fin 4 → K //
      MvPolynomial.eval y (theta5Chart4Pullback (K := K) r p) = 0} ≤
      16 * Fintype.card K ^ 3 := by
  classical
  let P := theta5Chart4Pullback (K := K) r p
  let Q : (Fin 4 → K) → Prop := fun y => MvPolynomial.eval y P = 0
  let q : NNRat := Fintype.card K
  have hp : P ≠ 0 := theta5Chart4Pullback_ne_zero r p hrp
  have hdegree : P.totalDegree ≤ 16 := theta5Chart4Pullback_degree_le r p
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : K)⟩)
  have hparam : Fintype.card {y : Fin 4 → K // Q y} =
      ({y ∈ Fintype.piFinset (fun _ : Fin 4 => (Finset.univ : Finset K)) |
        Q y}.card) := by
    rw [Fintype.card_subtype]
    simp [Q, Fintype.piFinset_univ]
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  have hsz' :
      (({y ∈ Fintype.piFinset (fun _ : Fin 4 => (Finset.univ : Finset K)) |
          Q y}.card : NNRat) / q ^ 4) ≤ (P.totalDegree : NNRat) / q := by
    simpa [Q, q] using hsz
  have hdegree' : (P.totalDegree : NNRat) ≤ 16 := by exact_mod_cast hdegree
  have hprob : (Fintype.card {y : Fin 4 → K // Q y} : NNRat) / q ^ 4 ≤ 16 / q := by
    rw [hparam]
    exact hsz'.trans ((div_le_div_iff_of_pos_right hq).2 hdegree')
  have hmul := (div_le_iff₀ (pow_pos hq 4)).mp hprob
  have hnat : (Fintype.card {y : Fin 4 → K // Q y} : NNRat) ≤
      16 * (Fintype.card K : NNRat) ^ 3 := by
    calc
      _ ≤ (16 / q) * q ^ 4 := hmul
      _ = 16 * (Fintype.card K : NNRat) ^ 3 := by
        dsimp [q]
        field_simp
  exact_mod_cast hnat

theorem theta5_hyperplane_zero_count_le (r : Fin 5 → ZMod 2) (hr : r ≠ 0) :
    Fintype.card {x : Fin 5 → K //
      (∑ i, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
      MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0} ≤
      16 * Fintype.card K ^ 3 := by
  classical
  have hp : ∃ p, r p ≠ 0 := by
    by_contra h
    push Not at h
    apply hr
    funext i
    exact h i
  obtain ⟨p, hp⟩ := hp
  exact (theta5_ambient_zeros_le_chart_zeros r p hp).trans
    (theta5_chart_zero_count_le r p hp)

theorem theta5_nonzero_binary_relations_card :
    Fintype.card {r : Fin 5 → ZMod 2 // r ≠ 0} = 31 := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ : Finset (Fin 5 → ZMod 2)).filter
      (fun r => r ≠ 0) = Finset.univ.erase 0 := by
    ext r
    simp
  rw [hset]
  norm_num

/-- The total number of dependent Θ₅ zeros is at most 31·16·q³. -/
theorem theta5_dependent_zero_count_le :
    Fintype.card {x : Fin 5 → K //
      MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0 ∧
      ∃ r : Fin 5 → ZMod 2, r ≠ 0 ∧
        (∑ i, algebraMap (ZMod 2) K (r i) * x i) = 0} ≤
      496 * Fintype.card K ^ 3 := by
  classical
  let R := {r : Fin 5 → ZMod 2 // r ≠ 0}
  let Fiber : R → Type _ := fun r => {x : Fin 5 → K //
    (∑ i, algebraMap (ZMod 2) K (r.val i) * x i) = 0 ∧
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0}
  let D := {x : Fin 5 → K //
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0 ∧
    ∃ r : Fin 5 → ZMod 2, r ≠ 0 ∧
      (∑ i, algebraMap (ZMod 2) K (r i) * x i) = 0}
  let witness : D → Σ r : R, Fiber r := fun x => by
    let r := Classical.choose x.property.2
    have hr := (Classical.choose_spec x.property.2).1
    have hxrel := (Classical.choose_spec x.property.2).2
    exact ⟨⟨r, hr⟩, ⟨x.val, hxrel, x.property.1⟩⟩
  have hwitness : Function.Injective witness := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Σ r : R, Fiber r => z.2.val) h
  have hsum : Fintype.card (Σ r : R, Fiber r) ≤
      ∑ r : R, (16 * Fintype.card K ^ 3) := by
    rw [Fintype.card_sigma]
    apply Finset.sum_le_sum
    intro r hr
    exact theta5_hyperplane_zero_count_le r.val r.property
  calc
    Fintype.card D ≤ Fintype.card (Σ r : R, Fiber r) :=
      Fintype.card_le_of_injective witness hwitness
    _ ≤ ∑ r : R, (16 * Fintype.card K ^ 3) := hsum
    _ = 496 * Fintype.card K ^ 3 := by
      rw [Finset.sum_const, Finset.card_univ, theta5_nonzero_binary_relations_card]
      ring

theorem theta5_independent_zero_exists_of_large_zero_count
    (hcount : Fintype.card {x : Fin 5 → K //
      MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0} >
      496 * Fintype.card K ^ 3) :
    ∃ x : Fin 5 → K,
      LinearIndependent (ZMod 2) x ∧
      MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0 := by
  classical
  let Z := {x : Fin 5 → K //
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0}
  let D := {x : Fin 5 → K //
    MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0 ∧
    ∃ r : Fin 5 → ZMod 2, r ≠ 0 ∧
      (∑ i, algebraMap (ZMod 2) K (r i) * x i) = 0}
  by_contra hnone
  have hall (x : Z) : ∃ r : Fin 5 → ZMod 2, r ≠ 0 ∧
      (∑ i, algebraMap (ZMod 2) K (r i) * x.val i) = 0 := by
    have hnot : ¬ LinearIndependent (ZMod 2) x.val := by
      intro hi
      exact hnone ⟨x.val, hi, x.property⟩
    rw [Fintype.linearIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨r, hsum, i, hi⟩ := hnot
    have hr : r ≠ 0 := by
      intro hz
      have := congrFun hz i
      exact hi this
    refine ⟨r, hr, ?_⟩
    simpa only [Algebra.smul_def] using hsum
  let f : Z → D := fun x => ⟨x.val, x.property, hall x⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : D => z.val) h)
  have hle : Fintype.card Z ≤ Fintype.card D := Fintype.card_le_of_injective f hinj
  have hdep : Fintype.card D ≤ 496 * Fintype.card K ^ 3 := by
    simpa [D] using (theta5_dependent_zero_count_le (K := K))
  change 496 * Fintype.card K ^ 3 < Fintype.card Z at hcount
  omega

theorem hasZeroSumSubspace_five_of_theta5_zero_count
    (hcount : Fintype.card {x : Fin 5 → K //
      MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0} >
      496 * Fintype.card K ^ 3) : HasZeroSumSubspace K 5 := by
  obtain ⟨x, hx, htheta⟩ := theta5_independent_zero_exists_of_large_zero_count hcount
  exact hasZeroSumSubspace_five_of_theta5_independent_zero x hx htheta

/-- Conditional assembly from the remaining global zero-count lower bound.
    The lower bound is explicitly a hypothesis, not a proved theorem here. -/
theorem oddCarletConjecture_of_remaining_theta5_zero_count
    (hcount : ∀ (n : ℕ), Odd n → 37 ≤ n →
      ¬ 5 ∣ n → ¬ 9 ∣ n → ¬ 11 ∣ n → ¬ 13 ∣ n → ¬ 17 ∣ n →
      ¬ 19 ∣ n → ¬ 21 ∣ n → ¬ 23 ∣ n → ¬ 29 ∣ n → ¬ 31 ∣ n →
      ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K],
        Fintype.card K = 2 ^ n →
        Fintype.card {x : Fin 5 → K //
          MvPolynomial.eval x (theta5.map (algebraMap (ZMod 2) K)) = 0} >
          496 * Fintype.card K ^ 3) : OddCarletConjecture := by
  apply oddCarletConjecture_of_remaining_theta5_independent_zeros
  intro n hn hmin h5 h9 h11 h13 h17 h19 h21 h23 h29 h31 K _ _ _ hcard
  classical
  exact theta5_independent_zero_exists_of_large_zero_count
    (hcount n hn hmin h5 h9 h11 h13 h17 h19 h21 h23 h29 h31 K hcard)

#print axioms theta5_ambient_zeros_le_chart_zeros
#print axioms theta5_chart_zero_count_le
#print axioms theta5_hyperplane_zero_count_le
#print axioms theta5_nonzero_binary_relations_card
#print axioms theta5_dependent_zero_count_le
#print axioms theta5_independent_zero_exists_of_large_zero_count
#print axioms hasZeroSumSubspace_five_of_theta5_zero_count
#print axioms oddCarletConjecture_of_remaining_theta5_zero_count
end Carlet
