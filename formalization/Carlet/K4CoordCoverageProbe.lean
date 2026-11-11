import Carlet.K4BadLocusSZProbe

noncomputable section
namespace Carlet

theorem neg_eq_self_of_char_two {K : Type*} [CommRing K] [CharP K 2] (a : K) :
    -a = a := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have honeadd : (1 : K) + 1 = 0 := by
    have htwo' : (2 : K) = (1 : K) + 1 := by ring
    rw [htwo'] at htwo
    exact htwo
  have hnegone : (-1 : K) = 1 := by
    calc
      -1 = -1 + 0 := by simp
      _ = -1 + ((1 : K) + 1) := by rw [← honeadd]
      _ = 1 := by ring
  calc
    -a = (-1) * a := by ring
    _ = 1 * a := by rw [hnegone]
    _ = a := by simp

set_option linter.style.haveILetI false in
theorem theta4HyperplaneCoordinates_covers
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) (x : Fin 4 → K)
    (hx : (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0) :
    ∃ y : Fin 3 → K, ∀ i,
      MvPolynomial.eval y (theta4HyperplaneCoordinates (K := K) r i) = x i := by
  classical
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  by_cases h0 : r 0 = 0
  · by_cases h1 : r 1 = 0
    · by_cases h2 : r 2 = 0
      · have h3 : r 3 = 1 := by
          have h3ne : r 3 ≠ 0 := by
            intro hz
            apply hr
            funext i
            fin_cases i <;> simp_all
          exact zmodTwo_eq_one_of_ne_zero _ h3ne
        have hx3 : x 3 = 0 := by
          simpa [Fin.sum_univ_succ, h0, h1, h2, h3] using hx
        refine ⟨fun i => x (Fin.castSucc i), ?_⟩
        intro i
        fin_cases i <;>
          simp [theta4HyperplaneCoordinates, h0, h1, h2, hx3]
      · have hr2 : r 2 = 1 := zmodTwo_eq_one_of_ne_zero _ h2
        have hx2 : x 2 = algebraMap (ZMod 2) K (r 3) * x 3 := by
          have hrel0 : algebraMap (ZMod 2) K (r 2) * x 2 +
              algebraMap (ZMod 2) K (r 3) * x 3 = 0 := by
            simpa [Fin.sum_univ_succ, h0, h1] using hx
          have hrel : x 2 + algebraMap (ZMod 2) K (r 3) * x 3 = 0 := by
            simpa [hr2] using hrel0
          calc
            x 2 = -(algebraMap (ZMod 2) K (r 3) * x 3) :=
              eq_neg_of_add_eq_zero_left hrel
            _ = algebraMap (ZMod 2) K (r 3) * x 3 :=
              neg_eq_self_of_char_two _
        refine ⟨fun i => if i = 0 then x 0 else if i = 1 then x 1 else x 3, ?_⟩
        intro i
        fin_cases i <;>
          simp [theta4HyperplaneCoordinates, theta4LinearForm, h0, h1, h2, hx2]
    · have hr1 : r 1 = 1 := zmodTwo_eq_one_of_ne_zero _ h1
      have hx1 : x 1 = algebraMap (ZMod 2) K (r 2) * x 2 +
          algebraMap (ZMod 2) K (r 3) * x 3 := by
        have hrel : algebraMap (ZMod 2) K (r 1) * x 1 +
            (algebraMap (ZMod 2) K (r 2) * x 2 +
            algebraMap (ZMod 2) K (r 3) * x 3) = 0 := by
          simpa [Fin.sum_univ_succ, h0] using hx
        have hrel' : x 1 + (algebraMap (ZMod 2) K (r 2) * x 2 +
            algebraMap (ZMod 2) K (r 3) * x 3) = 0 := by
          simpa [hr1] using hrel
        calc
          x 1 = -(algebraMap (ZMod 2) K (r 2) * x 2 +
              algebraMap (ZMod 2) K (r 3) * x 3) :=
            eq_neg_of_add_eq_zero_left hrel'
          _ = algebraMap (ZMod 2) K (r 2) * x 2 +
              algebraMap (ZMod 2) K (r 3) * x 3 :=
            neg_eq_self_of_char_two _
      refine ⟨fun i => if i = 0 then x 0 else if i = 1 then x 2 else x 3, ?_⟩
      intro i
      fin_cases i <;>
        simp [theta4HyperplaneCoordinates, theta4LinearForm, h0, h1, hx1]
  · have hr0 : r 0 = 1 := zmodTwo_eq_one_of_ne_zero _ h0
    have hx0 : x 0 = algebraMap (ZMod 2) K (r 1) * x 1 +
        (algebraMap (ZMod 2) K (r 2) * x 2 +
        algebraMap (ZMod 2) K (r 3) * x 3) := by
      have hrel : algebraMap (ZMod 2) K (r 0) * x 0 +
          (algebraMap (ZMod 2) K (r 1) * x 1 +
          (algebraMap (ZMod 2) K (r 2) * x 2 +
          algebraMap (ZMod 2) K (r 3) * x 3)) = 0 := by
        simpa [Fin.sum_univ_succ] using hx
      have hrel' : x 0 + (algebraMap (ZMod 2) K (r 1) * x 1 +
          (algebraMap (ZMod 2) K (r 2) * x 2 +
          algebraMap (ZMod 2) K (r 3) * x 3)) = 0 := by
        simpa [hr0] using hrel
      calc
        x 0 = -(algebraMap (ZMod 2) K (r 1) * x 1 +
            (algebraMap (ZMod 2) K (r 2) * x 2 +
            algebraMap (ZMod 2) K (r 3) * x 3)) :=
          eq_neg_of_add_eq_zero_left hrel'
        _ = algebraMap (ZMod 2) K (r 1) * x 1 +
            (algebraMap (ZMod 2) K (r 2) * x 2 +
            algebraMap (ZMod 2) K (r 3) * x 3) :=
          neg_eq_self_of_char_two _
    refine ⟨fun i => x i.succ, ?_⟩
    intro i
    fin_cases i <;>
      simp [theta4HyperplaneCoordinates, theta4LinearForm, hr0, hx0, ← add_assoc]

theorem theta4HyperplaneCoordinates_eval_injective
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    Function.Injective (fun y : Fin 3 → K =>
      fun i => MvPolynomial.eval y (theta4HyperplaneCoordinates (K := K) r i)) := by
  classical
  intro y z h
  by_cases h0 : r 0 = 0
  · by_cases h1 : r 1 = 0
    · by_cases h2 : r 2 = 0
      · have h3 : r 3 ≠ 0 := by
          intro hz
          apply hr
          funext i
          fin_cases i <;> simp_all
        have he0 := congrFun h (0 : Fin 4)
        have he1 := congrFun h (1 : Fin 4)
        have he2 := congrFun h (2 : Fin 4)
        have hy0 : y 0 = z 0 := by
          simpa [theta4HyperplaneCoordinates, h0, h1, h2] using he0
        have hy1 : y 1 = z 1 := by
          simpa [theta4HyperplaneCoordinates, h0, h1, h2] using he1
        have hy2 : y 2 = z 2 := by
          simpa [theta4HyperplaneCoordinates, h0, h1, h2] using he2
        funext i
        fin_cases i <;> assumption
      · have he0 := congrFun h (0 : Fin 4)
        have he1 := congrFun h (1 : Fin 4)
        have he3 := congrFun h (3 : Fin 4)
        have hy0 : y 0 = z 0 := by
          simpa [theta4HyperplaneCoordinates, h0, h1] using he0
        have hy1 : y 1 = z 1 := by
          simpa [theta4HyperplaneCoordinates, h0, h1] using he1
        have hy2 : y 2 = z 2 := by
          simpa [theta4HyperplaneCoordinates, h0, h1, h2] using he3
        funext i
        fin_cases i <;> assumption
    · have he0 := congrFun h (0 : Fin 4)
      have he2 := congrFun h (2 : Fin 4)
      have he3 := congrFun h (3 : Fin 4)
      have hy0 : y 0 = z 0 := by
        simpa [theta4HyperplaneCoordinates, h0] using he0
      have hy1 : y 1 = z 1 := by
        simpa [theta4HyperplaneCoordinates, h0, h1] using he2
      have hy2 : y 2 = z 2 := by
        simpa [theta4HyperplaneCoordinates, h0, h1] using he3
      funext i
      fin_cases i <;> assumption
  · have he1 := congrFun h (1 : Fin 4)
    have he2 := congrFun h (2 : Fin 4)
    have he3 := congrFun h (3 : Fin 4)
    have hy0 : y 0 = z 0 := by
      simpa [theta4HyperplaneCoordinates, h0] using he1
    have hy1 : y 1 = z 1 := by
      simpa [theta4HyperplaneCoordinates, h0] using he2
    have hy2 : y 2 = z 2 := by
      simpa [theta4HyperplaneCoordinates, h0] using he3
    funext i
    fin_cases i <;> assumption

set_option linter.style.haveILetI false in
theorem theta4HyperplaneCoordinates_eval_in_kernel
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) (y : Fin 3 → K) :
    (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) *
      MvPolynomial.eval y (theta4HyperplaneCoordinates (K := K) r i)) = 0 := by
  classical
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hdouble (a : K) : a + a = 0 := by
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc
      a + a = (2 : K) * a := (two_mul a).symm
      _ = 0 := by rw [htwo]; simp
  have hcoeff (a : ZMod 2) :
      algebraMap (ZMod 2) K a * algebraMap (ZMod 2) K a =
        algebraMap (ZMod 2) K a := by
    have ha : a * a = a := by fin_cases a <;> rfl
    rw [← map_mul, ha]
  by_cases h0 : r 0 = 0
  · by_cases h1 : r 1 = 0
    · by_cases h2 : r 2 = 0
      · have h3 : r 3 = 1 := by
          have h3ne : r 3 ≠ 0 := by
            intro hz
            apply hr
            funext i
            fin_cases i <;> simp_all
          exact zmodTwo_eq_one_of_ne_zero _ h3ne
        have he3 : MvPolynomial.eval y
            (theta4HyperplaneCoordinates (K := K) r 3) = 0 := by
          simp [theta4HyperplaneCoordinates, h0, h1, h2]
        simp [Fin.sum_univ_succ, h0, h1, h2, h3, he3]
      · have hr2 : r 2 = 1 := zmodTwo_eq_one_of_ne_zero _ h2
        simp only [Fin.sum_univ_succ]
        simp [theta4HyperplaneCoordinates, theta4LinearForm, h0, h1, hr2,
          hdouble]
    · have hr1 : r 1 = 1 := zmodTwo_eq_one_of_ne_zero _ h1
      simp only [Fin.sum_univ_succ]
      simp [theta4HyperplaneCoordinates, theta4LinearForm, h0, hr1, hdouble]
  · have hr0 : r 0 = 1 := zmodTwo_eq_one_of_ne_zero _ h0
    simp only [Fin.sum_univ_succ]
    simp [theta4HyperplaneCoordinates, theta4LinearForm, hr0]
    have ha := hdouble (algebraMap (ZMod 2) K (r 1) * y 0)
    have hb := hdouble (algebraMap (ZMod 2) K (r 2) * y 1)
    have hc := hdouble (algebraMap (ZMod 2) K (r 3) * y 2)
    linear_combination ha + hb + hc

noncomputable def theta4HyperplaneKernelEquiv
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    (Fin 3 → K) ≃ {x : Fin 4 → K //
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0} := by
  classical
  apply Equiv.ofBijective
    (fun y => ⟨(fun i => MvPolynomial.eval y
      (theta4HyperplaneCoordinates (K := K) r i)),
      theta4HyperplaneCoordinates_eval_in_kernel r hr y⟩)
  constructor
  · intro y z h
    apply theta4HyperplaneCoordinates_eval_injective r hr
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨y, hy⟩ := theta4HyperplaneCoordinates_covers r hr x.val x.property
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact funext hy

set_option linter.style.haveILetI false in
theorem theta4HyperplaneKernel_card
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    Fintype.card {x : Fin 4 → K //
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0} =
      Fintype.card K ^ 3 := by
  classical
  rw [← Fintype.card_congr (theta4HyperplaneKernelEquiv r hr)]
  simp

set_option maxHeartbeats 1000000 in
noncomputable def theta4HyperplaneZeroEquiv
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    {y : Fin 3 → K // MvPolynomial.eval y
        (theta4Pullback (theta4HyperplaneCoordinates (K := K) r)) = 0} ≃
      {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} := by
  classical
  let f : {y : Fin 3 → K // MvPolynomial.eval y
      (theta4Pullback (theta4HyperplaneCoordinates (K := K) r)) = 0} →
      {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} :=
    fun y => ⟨(fun i => MvPolynomial.eval y.val
      (theta4HyperplaneCoordinates (K := K) r i)),
      ⟨theta4HyperplaneCoordinates_eval_in_kernel r hr y.val, by
        have hzero := y.property
        rw [theta4Pullback_eval] at hzero
        exact hzero⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro y z h
      apply Subtype.ext
      apply theta4HyperplaneCoordinates_eval_injective r hr
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨y, hy⟩ := theta4HyperplaneCoordinates_covers r hr x.val x.property.1
      have hcoords : (fun i => MvPolynomial.eval y
          (theta4HyperplaneCoordinates (K := K) r i)) = x.val := funext hy
      have hroot : MvPolynomial.eval y
          (theta4Pullback (theta4HyperplaneCoordinates (K := K) r)) = 0 := by
        rw [theta4Pullback_eval, hcoords]
        exact x.property.2
      exact ⟨⟨y, hroot⟩, Subtype.ext hcoords⟩
  exact Equiv.ofBijective f hf

set_option maxHeartbeats 1000000 in
theorem theta4HyperplaneZeroSet_card_eq
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    Fintype.card {y : Fin 3 → K // MvPolynomial.eval y
        (theta4Pullback (theta4HyperplaneCoordinates (K := K) r)) = 0} =
    Fintype.card {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} := by
  classical
  rw [Fintype.card_congr (theta4HyperplaneZeroEquiv r hr)]

theorem theta4HyperplanePullback_ne_zero
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    theta4Pullback (theta4HyperplaneCoordinates (K := K) r) ≠ 0 := by
  apply theta4Pullback_ne_zero_of_covering_hyperplane
  intro x hx
  exact theta4HyperplaneCoordinates_covers r hr x hx

theorem theta4HyperplanePullback_degree_le
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) :
    (theta4Pullback (theta4HyperplaneCoordinates (K := K) r)).totalDegree ≤ 8 := by
  apply theta4Pullback_totalDegree_le
  exact theta4HyperplaneCoordinates_degree_le r

theorem theta4HyperplanePullback_zero_probability_bound
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    (({y ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset K)) |
        MvPolynomial.eval y
          (theta4Pullback (theta4HyperplaneCoordinates (K := K) r)) = 0}.card : NNRat) /
        (Fintype.card K : NNRat)^3) ≤ 8 / (Fintype.card K : NNRat) := by
  let p := theta4Pullback (theta4HyperplaneCoordinates (K := K) r)
  have hp : p ≠ 0 := theta4HyperplanePullback_ne_zero r hr
  have hdegree : p.totalDegree ≤ 8 := theta4HyperplanePullback_degree_le r
  have hsz := mvPolynomial_zero_probability_bound p hp Finset.univ
  have hsz' :
      (({y ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset K)) |
          MvPolynomial.eval y p = 0}.card : NNRat) /
        (Fintype.card K : NNRat)^3) ≤
        (p.totalDegree : NNRat) / (Fintype.card K : NNRat) := by
    simpa using hsz
  have hdegree' : (p.totalDegree : NNRat) ≤ 8 := by exact_mod_cast hdegree
  have hcard : 0 < (Fintype.card K : NNRat) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : K)⟩)
  calc
    _ ≤ (p.totalDegree : NNRat) / (Fintype.card K : NNRat) := hsz'
    _ ≤ 8 / (Fintype.card K : NNRat) :=
      (div_le_div_iff_of_pos_right hcard).2 hdegree'

set_option maxHeartbeats 1000000 in
theorem theta4HyperplaneAmbientZero_fraction_bound
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    ((Fintype.card {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} : NNRat) /
        (Fintype.card K : NNRat)^3) ≤ 8 / (Fintype.card K : NNRat) := by
  let p := theta4Pullback (theta4HyperplaneCoordinates (K := K) r)
  let Q : (Fin 3 → K) → Prop := fun y => MvPolynomial.eval y p = 0
  have hparam : Fintype.card {y : Fin 3 → K // Q y} =
      ({y ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset K)) |
        Q y}.card) := by
    rw [Fintype.card_subtype]
    simp [Q, Fintype.piFinset_univ]
  have hcount :
      Fintype.card {y : Fin 3 → K // Q y} =
      Fintype.card {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} := by
    exact theta4HyperplaneZeroSet_card_eq r hr
  have hprob :
      (({y ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset K)) |
          Q y}.card : NNRat) / (Fintype.card K : NNRat)^3) ≤
        8 / (Fintype.card K : NNRat) := by
    simpa [Q, p] using theta4HyperplanePullback_zero_probability_bound r hr
  calc
    _ = ((Fintype.card {y : Fin 3 → K // Q y} : NNRat) /
        (Fintype.card K : NNRat)^3) := by rw [hcount]
    _ = (({y ∈ Fintype.piFinset
        (fun _ : Fin 3 => (Finset.univ : Finset K)) | Q y}.card : NNRat) /
        (Fintype.card K : NNRat)^3) := by rw [hparam]
    _ ≤ 8 / (Fintype.card K : NNRat) := hprob

set_option maxRecDepth 10000 in
theorem theta4HyperplaneAmbientZero_count_le
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    (Fintype.card {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} : NNRat) ≤
      8 * (Fintype.card K : NNRat)^2 := by
  let q : NNRat := Fintype.card K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : K)⟩)
  have hprob := theta4HyperplaneAmbientZero_fraction_bound (K := K) r hr
  change (Fintype.card {x : Fin 4 → K //
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} : NNRat) /
      q^3 ≤ 8 / q at hprob
  have hmul := (div_le_iff₀ (pow_pos hq 3)).mp hprob
  calc
    _ ≤ (8 / q) * q^3 := hmul
    _ = 8 * (Fintype.card K : NNRat)^2 := by
      dsimp [q]
      field_simp

theorem theta4HyperplaneAmbientZero_count_le_nat
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (r : Fin 4 → ZMod 2) (hr : r ≠ 0) :
    Fintype.card {x : Fin 4 → K //
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} ≤
      8 * Fintype.card K ^ 2 := by
  exact_mod_cast theta4HyperplaneAmbientZero_count_le r hr

theorem theta4_nonzero_binary_relations_card :
    Fintype.card {r : Fin 4 → ZMod 2 // r ≠ 0} = 15 := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ : Finset (Fin 4 → ZMod 2)).filter
      (fun r => r ≠ 0) = Finset.univ.erase 0 := by
    ext r
    simp
  rw [hset]
  norm_num

theorem theta4_dependent_zero_count_le
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K] :
    Fintype.card {x : Fin 4 → K //
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0 ∧
        ∃ r : Fin 4 → ZMod 2, r ≠ 0 ∧
          (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0} ≤
      120 * Fintype.card K ^ 2 := by
  classical
  let R := {r : Fin 4 → ZMod 2 // r ≠ 0}
  let Fiber : R → Type _ := fun r => {x : Fin 4 → K //
    (∑ i : Fin 4, algebraMap (ZMod 2) K (r.val i) * x i) = 0 ∧
    MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0}
  let D := {x : Fin 4 → K //
    MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0 ∧
    ∃ r : Fin 4 → ZMod 2, r ≠ 0 ∧
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0}
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
      ∑ r : R, (8 * Fintype.card K ^ 2) := by
    rw [Fintype.card_sigma]
    apply Finset.sum_le_sum
    intro r hr
    exact theta4HyperplaneAmbientZero_count_le_nat r.val r.property
  calc
    Fintype.card D ≤ Fintype.card (Σ r : R, Fiber r) :=
      Fintype.card_le_of_injective witness hwitness
    _ ≤ ∑ r : R, (8 * Fintype.card K ^ 2) := hsum
    _ = 120 * Fintype.card K ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, theta4_nonzero_binary_relations_card]
      ring

theorem theta4_independent_zero_exists_of_large_zero_count
    {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (hcount : Fintype.card {x : Fin 4 → K //
        MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} >
      120 * Fintype.card K ^ 2) :
    ∃ x : Fin 4 → K,
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0 ∧
      ∀ r : Fin 4 → ZMod 2, r ≠ 0 →
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) ≠ 0 := by
  classical
  let Z := {x : Fin 4 → K //
    MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0}
  let D := {x : Fin 4 → K //
    MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0 ∧
    ∃ r : Fin 4 → ZMod 2, r ≠ 0 ∧
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0}
  have hnotAll : ¬ ∀ x : Z,
      ∃ r : Fin 4 → ZMod 2, r ≠ 0 ∧
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x.val i) = 0 := by
    intro hall
    let f : Z → D := fun x => ⟨x.val, x.property, hall x⟩
    have hf : Function.Injective f := by
      intro x y h
      have hv : (f x).val = (f y).val := congrArg (fun z : D => z.val) h
      exact Subtype.ext hv
    have hle : Fintype.card Z ≤ Fintype.card D :=
      Fintype.card_le_of_injective f hf
    change Fintype.card {x : Fin 4 → K //
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} ≤
      Fintype.card D at hle
    have hdep : Fintype.card D ≤ 120 * Fintype.card K ^ 2 := by
      simpa [D] using theta4_dependent_zero_count_le (K := K)
    omega
  push Not at hnotAll
  obtain ⟨x, hx⟩ := hnotAll
  refine ⟨x.val, x.property, ?_⟩
  intro r hr hrel
  exact (hx r hr) hrel

#print axioms theta4HyperplaneCoordinates_covers
#print axioms theta4HyperplaneCoordinates_eval_injective
#print axioms theta4HyperplaneCoordinates_eval_in_kernel
#print axioms theta4HyperplaneKernelEquiv
#print axioms theta4HyperplaneKernel_card
#print axioms theta4HyperplaneZeroEquiv
#print axioms theta4HyperplaneZeroSet_card_eq
#print axioms theta4HyperplaneAmbientZero_fraction_bound
#print axioms theta4HyperplaneAmbientZero_count_le
#print axioms theta4HyperplaneAmbientZero_count_le_nat
#print axioms theta4_nonzero_binary_relations_card
#print axioms theta4_dependent_zero_count_le
#print axioms theta4_independent_zero_exists_of_large_zero_count
#print axioms theta4HyperplanePullback_ne_zero
#print axioms theta4HyperplanePullback_degree_le
#print axioms theta4HyperplanePullback_zero_probability_bound
#print axioms theta4HyperplaneAmbientZero_fraction_bound
end Carlet
