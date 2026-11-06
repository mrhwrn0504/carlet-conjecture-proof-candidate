import Carlet.K4ThetaProbe
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! A verified component of the low-dimensional Θ₄ counting route.

The published Θ₄ argument subtracts the dependent tuples from the total
zero count.  This file starts formalizing that exclusion side using mathlib's
Schwartz–Zippel theorem; it does not assume the missing Lang–Weil lower bound.
-/

noncomputable section
set_option maxRecDepth 10000

namespace Carlet

def theta4ExponentTermPoly (l : List (Fin 4 × ℕ)) :
    MvPolynomial (Fin 4) (ZMod 2) :=
  (l.map (fun p => (MvPolynomial.X p.1 : MvPolynomial (Fin 4) (ZMod 2)) ^ p.2)).prod

def theta4ExponentTerms : List (List (Fin 4 × ℕ)) :=
  [ [(0,8)], [(1,8)], [(2,8)], [(3,8)],
    [(0,4),(1,4)], [(0,4),(2,4)], [(0,4),(3,4)],
    [(1,4),(2,4)], [(1,4),(3,4)], [(2,4),(3,4)],
    [(1,4),(2,2),(3,2)], [(1,2),(2,4),(3,2)], [(1,2),(2,2),(3,4)],
    [(0,4),(2,2),(3,2)], [(0,2),(2,4),(3,2)], [(0,2),(2,2),(3,4)],
    [(0,4),(1,2),(3,2)], [(0,2),(1,4),(3,2)], [(0,2),(1,2),(3,4)],
    [(0,4),(1,2),(2,2)], [(0,2),(1,4),(2,2)], [(0,2),(1,2),(2,4)],
    [(0,4),(1,2),(2,1),(3,1)], [(0,4),(2,2),(1,1),(3,1)],
    [(0,4),(3,2),(1,1),(2,1)], [(1,4),(0,2),(2,1),(3,1)],
    [(1,4),(2,2),(0,1),(3,1)], [(1,4),(3,2),(0,1),(2,1)],
    [(2,4),(0,2),(1,1),(3,1)], [(2,4),(1,2),(0,1),(3,1)],
    [(2,4),(3,2),(0,1),(1,1)], [(3,4),(0,2),(1,1),(2,1)],
    [(3,4),(1,2),(0,1),(2,1)], [(3,4),(2,2),(0,1),(1,1)],
    [(0,2),(1,2),(2,2),(3,2)] ]

theorem theta4_eq_exponent_term_sum :
    theta4 = (theta4ExponentTerms.map theta4ExponentTermPoly).sum := by
  simp [theta4, theta4ExponentTerms, theta4ExponentTermPoly, k4X]
  ring

theorem totalDegree_list_product_powers_le
    (l : List (Fin 4 × ℕ)) :
    ((l.map (fun p => (MvPolynomial.X p.1 : MvPolynomial (Fin 4) (ZMod 2)) ^ p.2)).prod).totalDegree ≤
      (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      calc
        ((MvPolynomial.X p.1 : MvPolynomial (Fin 4) (ZMod 2)) ^ p.2 *
            (ps.map (fun q => (MvPolynomial.X q.1 : MvPolynomial (Fin 4) (ZMod 2)) ^ q.2)).prod).totalDegree
            ≤ ((MvPolynomial.X p.1 : MvPolynomial (Fin 4) (ZMod 2)) ^ p.2).totalDegree +
                ((ps.map (fun q => (MvPolynomial.X q.1 : MvPolynomial (Fin 4) (ZMod 2)) ^ q.2)).prod).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
        _ ≤ p.2 + (ps.map Prod.snd).sum := by
              exact Nat.add_le_add (by simp [MvPolynomial.totalDegree_X_pow]) ih

def theta4ExponentTermPolyOver {σ R : Type*} [CommSemiring R]
    (f : Fin 4 → MvPolynomial σ R) (l : List (Fin 4 × ℕ)) :
    MvPolynomial σ R :=
  (l.map (fun p => f p.1 ^ p.2)).prod

theorem totalDegree_list_product_powers_le_of_linear
    {σ R : Type*} [CommSemiring R]
    (f : Fin 4 → MvPolynomial σ R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (l : List (Fin 4 × ℕ)) :
    (theta4ExponentTermPolyOver f l).totalDegree ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => simp [theta4ExponentTermPolyOver]
  | cons p ps ih =>
      simp only [theta4ExponentTermPolyOver, List.map_cons, List.prod_cons,
        List.sum_cons]
      calc
        (f p.1 ^ p.2 * (ps.map (fun q => f q.1 ^ q.2)).prod).totalDegree
            ≤ (f p.1 ^ p.2).totalDegree +
                ((ps.map (fun q => f q.1 ^ q.2)).prod).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
        _ ≤ p.2 + (ps.map Prod.snd).sum := by
              apply Nat.add_le_add
              · calc
                  (f p.1 ^ p.2).totalDegree ≤ p.2 * (f p.1).totalDegree :=
                    MvPolynomial.totalDegree_pow _ _
                  _ ≤ p.2 := by simpa using Nat.mul_le_mul_left p.2 (hf p.1)
              · exact ih

theorem totalDegree_list_sum_le
    {σ R : Type*} [CommSemiring R] (l : List (MvPolynomial σ R)) :
    l.sum.totalDegree ≤ (l.map MvPolynomial.totalDegree).foldr max 0 := by
  induction l with
  | nil => simp
  | cons p ps ih =>
      simp only [List.sum_cons, List.map_cons, List.foldr_cons]
      exact le_trans (MvPolynomial.totalDegree_add _ _)
        (max_le (le_max_left _ _)
          (le_trans ih (le_max_right _ _)))

theorem list_foldr_max_map_mono {α : Type*} (l : List α)
    (f g : α → ℕ) (hfg : ∀ a, f a ≤ g a) :
    (l.map f).foldr max 0 ≤ (l.map g).foldr max 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le
        (le_trans (hfg a) (le_max_left _ _))
        (le_trans ih (le_max_right _ _))

theorem theta4_totalDegree_le : theta4.totalDegree ≤ 8 := by
  have hmono : ∀ l : List (Fin 4 × ℕ),
      (theta4ExponentTermPoly l).totalDegree ≤ (l.map Prod.snd).sum := by
    intro l
    simpa [theta4ExponentTermPoly] using totalDegree_list_product_powers_le l
  have hmax :
      (theta4ExponentTerms.map (fun l => (l.map Prod.snd).sum)).foldr max 0 ≤ 8 := by
    norm_num [theta4ExponentTerms]
  calc
    theta4.totalDegree = (theta4ExponentTerms.map theta4ExponentTermPoly).sum.totalDegree := by
      rw [theta4_eq_exponent_term_sum]
    _ ≤ ((theta4ExponentTerms.map theta4ExponentTermPoly).map MvPolynomial.totalDegree).foldr max 0 :=
      totalDegree_list_sum_le _
    _ ≤ (theta4ExponentTerms.map (fun l => (l.map Prod.snd).sum)).foldr max 0 := by
      simpa [List.map_map, Function.comp_def] using
        list_foldr_max_map_mono theta4ExponentTerms
          (fun l => (theta4ExponentTermPoly l).totalDegree)
          (fun l => (l.map Prod.snd).sum) hmono
    _ ≤ 8 := hmax

def theta4Pullback {σ R : Type*} [CommSemiring R]
    (f : Fin 4 → MvPolynomial σ R) : MvPolynomial σ R :=
  (theta4ExponentTerms.map (theta4ExponentTermPolyOver f)).sum

theorem theta4Pullback_totalDegree_le
    {σ R : Type*} [CommSemiring R]
    (f : Fin 4 → MvPolynomial σ R) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (theta4Pullback f).totalDegree ≤ 8 := by
  have hmono : ∀ l : List (Fin 4 × ℕ),
      (theta4ExponentTermPolyOver f l).totalDegree ≤ (l.map Prod.snd).sum := by
    intro l
    exact totalDegree_list_product_powers_le_of_linear f hf l
  have hmax :
      (theta4ExponentTerms.map (fun l => (l.map Prod.snd).sum)).foldr max 0 ≤ 8 := by
    norm_num [theta4ExponentTerms]
  calc
    (theta4Pullback f).totalDegree ≤
        ((theta4ExponentTerms.map (theta4ExponentTermPolyOver f)).map
          MvPolynomial.totalDegree).foldr max 0 := by
      exact totalDegree_list_sum_le _
    _ ≤ (theta4ExponentTerms.map (fun l => (l.map Prod.snd).sum)).foldr max 0 := by
      simpa [List.map_map, Function.comp_def] using
        list_foldr_max_map_mono theta4ExponentTerms
          (fun l => (theta4ExponentTermPolyOver f l).totalDegree)
          (fun l => (l.map Prod.snd).sum) hmono
    _ ≤ 8 := hmax

theorem theta4ExponentTermPolyOver_eval
    {σ K : Type*} [CommSemiring K] [Algebra (ZMod 2) K]
    (f : Fin 4 → MvPolynomial σ K) (y : σ → K)
    (l : List (Fin 4 × ℕ)) :
    MvPolynomial.eval y (theta4ExponentTermPolyOver f l) =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K)
        (fun i => MvPolynomial.eval y (f i)) (theta4ExponentTermPoly l) := by
  induction l with
  | nil => simp [theta4ExponentTermPolyOver, theta4ExponentTermPoly]
  | cons p ps ih =>
      simp only [theta4ExponentTermPolyOver, theta4ExponentTermPoly,
        List.map_cons, List.prod_cons]
      simp only [theta4ExponentTermPolyOver, theta4ExponentTermPoly] at ih
      rw [MvPolynomial.eval_mul, MvPolynomial.eval₂_mul,
        MvPolynomial.eval_pow, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_X, ih]

theorem eval_theta4ExponentTermPolyOver_list
    {σ K : Type*} [CommSemiring K] [Algebra (ZMod 2) K]
    (f : Fin 4 → MvPolynomial σ K) (y : σ → K)
    (ls : List (List (Fin 4 × ℕ))) :
    MvPolynomial.eval y ((ls.map (theta4ExponentTermPolyOver f)).sum) =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K)
        (fun i => MvPolynomial.eval y (f i))
        ((ls.map theta4ExponentTermPoly).sum) := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
      simp only [List.map_cons, List.sum_cons, map_add, MvPolynomial.eval₂_add]
      rw [theta4ExponentTermPolyOver_eval, ih]

theorem theta4Pullback_eval
    {σ K : Type*} [CommSemiring K] [Algebra (ZMod 2) K]
    (f : Fin 4 → MvPolynomial σ K) (y : σ → K) :
    MvPolynomial.eval y (theta4Pullback f) =
      MvPolynomial.eval (fun i => MvPolynomial.eval y (f i))
        (theta4.map (algebraMap (ZMod 2) K)) := by
  rw [theta4Pullback, theta4_eq_exponent_term_sum, MvPolynomial.eval_map]
  exact eval_theta4ExponentTermPolyOver_list f y theta4ExponentTerms

theorem theta4_eval_second_unit :
    MvPolynomial.eval (fun i : Fin 4 => if i = 1 then (1 : ZMod 2) else 0) theta4 = 1 := by
  norm_num [theta4, k4X]
  decide

theorem theta4_eval_first_two_units :
    MvPolynomial.eval (fun i : Fin 4 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) theta4 = 1 := by
  norm_num [theta4, k4X]
  decide

theorem theta4_f2_hyperplane_has_nonzero_value (r : Fin 4 → ZMod 2) :
    ∃ x : Fin 4 → ZMod 2,
      (∑ i : Fin 4, r i * x i) = 0 ∧
      MvPolynomial.eval x theta4 = 1 := by
  by_cases h0 : r 0 = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_, theta4_eval_first_unit⟩
    simp [h0]
  · by_cases h1 : r 1 = 0
    · refine ⟨fun i => if i = 1 then 1 else 0, ?_, theta4_eval_second_unit⟩
      simp [h1]
    · refine ⟨fun i => if i = 0 ∨ i = 1 then 1 else 0, ?_, theta4_eval_first_two_units⟩
      have hr0 : r 0 = 1 := by
        generalize hval : r 0 = a
        fin_cases a
        · exact False.elim (h0 hval)
        · rfl
      have hr1 : r 1 = 1 := by
        generalize hval : r 1 = a
        fin_cases a
        · exact False.elim (h1 hval)
        · rfl
      simp [Fin.sum_univ_succ, hr0, hr1]
      decide

theorem theta4_eval_first_unit_over_field
    {K : Type*} [Field K] [Algebra (ZMod 2) K] :
    MvPolynomial.eval (fun i : Fin 4 => if i = 0 then (1 : K) else 0)
      (theta4.map (algebraMap (ZMod 2) K)) = 1 := by
  simp [theta4, k4X]

theorem theta4_eval_second_unit_over_field
    {K : Type*} [Field K] [Algebra (ZMod 2) K] :
    MvPolynomial.eval (fun i : Fin 4 => if i = 1 then (1 : K) else 0)
      (theta4.map (algebraMap (ZMod 2) K)) = 1 := by
  simp [theta4, k4X]

theorem one_add_one_eq_zero_over_field
    {K : Type*} [Field K] [Algebra (ZMod 2) K] :
    (1 : K) + 1 = 0 := by
  have h := congrArg (algebraMap (ZMod 2) K)
    (show (1 : ZMod 2) + 1 = 0 by decide)
  simpa using h

theorem theta4_eval_first_two_units_over_field
    {K : Type*} [Field K] [Algebra (ZMod 2) K] :
    MvPolynomial.eval (fun i : Fin 4 => if i = 0 ∨ i = 1 then (1 : K) else 0)
      (theta4.map (algebraMap (ZMod 2) K)) = 1 := by
  simp [theta4, k4X, one_add_one_eq_zero_over_field]

theorem theta4_field_hyperplane_has_nonzero_value
    {K : Type*} [Field K] [Algebra (ZMod 2) K] (r : Fin 4 → ZMod 2) :
    ∃ x : Fin 4 → K,
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 ∧
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 1 := by
  by_cases h0 : r 0 = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_, theta4_eval_first_unit_over_field⟩
    simp [h0]
  · by_cases h1 : r 1 = 0
    · refine ⟨fun i => if i = 1 then 1 else 0, ?_, theta4_eval_second_unit_over_field⟩
      simp [h1]
    · refine ⟨fun i => if i = 0 ∨ i = 1 then 1 else 0, ?_,
        theta4_eval_first_two_units_over_field⟩
      have hr0 : r 0 = 1 := by
        generalize hval : r 0 = a
        fin_cases a
        · exact False.elim (h0 hval)
        · rfl
      have hr1 : r 1 = 1 := by
        generalize hval : r 1 = a
        fin_cases a
        · exact False.elim (h1 hval)
        · rfl
      calc
        (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) *
            (if i = 0 ∨ i = 1 then (1 : K) else 0)) =
            algebraMap (ZMod 2) K (r 0 + r 1) := by
          simp [Fin.sum_univ_succ]
        _ = 0 := by rw [hr0, hr1]; simp [one_add_one_eq_zero_over_field]

theorem theta4Pullback_ne_zero_of_covering_hyperplane
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (r : Fin 4 → ZMod 2) (f : Fin 4 → MvPolynomial (Fin 3) K)
    (hcover : ∀ x : Fin 4 → K,
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 →
      ∃ y : Fin 3 → K, ∀ i, MvPolynomial.eval y (f i) = x i) :
    theta4Pullback f ≠ 0 := by
  obtain ⟨x, hx, htheta⟩ := theta4_field_hyperplane_has_nonzero_value (K := K) r
  obtain ⟨y, hy⟩ := hcover x hx
  have hval : MvPolynomial.eval y (theta4Pullback f) = 1 := by
    rw [theta4Pullback_eval]
    simpa [hy] using htheta
  intro hzero
  rw [hzero] at hval
  simp at hval

def theta4LinearForm {K : Type*} [CommSemiring K] [Algebra (ZMod 2) K]
    (a : Fin 3 → K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C (a 0) * MvPolynomial.X 0 +
    MvPolynomial.C (a 1) * MvPolynomial.X 1 +
    MvPolynomial.C (a 2) * MvPolynomial.X 2

theorem totalDegree_linearTerm_le_one
    {K : Type*} [CommSemiring K] [Nontrivial K] [Algebra (ZMod 2) K]
    (a : K) (i : Fin 3) :
    (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := by
  calc
    (MvPolynomial.C a * MvPolynomial.X i).totalDegree ≤
        (MvPolynomial.C a).totalDegree + (MvPolynomial.X i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp

theorem totalDegree_theta4LinearForm_le_one
    {K : Type*} [CommSemiring K] [Nontrivial K] [Algebra (ZMod 2) K]
    (a : Fin 3 → K) : (theta4LinearForm a).totalDegree ≤ 1 := by
  have h0 := totalDegree_linearTerm_le_one (a 0) (0 : Fin 3)
  have h1 := totalDegree_linearTerm_le_one (a 1) (1 : Fin 3)
  have h2 := totalDegree_linearTerm_le_one (a 2) (2 : Fin 3)
  have hadd : ∀ p q : MvPolynomial (Fin 3) K,
      p.totalDegree ≤ 1 → q.totalDegree ≤ 1 → (p + q).totalDegree ≤ 1 := by
    intro p q hp hq
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hp hq)
  unfold theta4LinearForm
  exact hadd _ _ (hadd _ _ h0 h1) h2

def theta4HyperplaneCoordinates {K : Type*} [CommSemiring K]
    [Algebra (ZMod 2) K] (r : Fin 4 → ZMod 2) :
    Fin 4 → MvPolynomial (Fin 3) K := fun i =>
  if r 0 = 0 then
    if r 1 = 0 then
      if r 2 = 0 then
        if i = 0 then MvPolynomial.X 0 else
        if i = 1 then MvPolynomial.X 1 else
        if i = 2 then MvPolynomial.X 2 else 0
      else if i = 0 then MvPolynomial.X 0 else
        if i = 1 then MvPolynomial.X 1 else
        if i = 2 then theta4LinearForm (fun j =>
          if j = 2 then algebraMap (ZMod 2) K (r 3) else 0) else MvPolynomial.X 2
    else if i = 0 then MvPolynomial.X 0 else
      if i = 1 then theta4LinearForm (fun j =>
        if j = 1 then algebraMap (ZMod 2) K (r 2)
        else if j = 2 then algebraMap (ZMod 2) K (r 3) else 0) else
      if i = 2 then MvPolynomial.X 1 else MvPolynomial.X 2
  else if i = 0 then theta4LinearForm (fun j =>
      if j = 0 then algebraMap (ZMod 2) K (r 1)
      else if j = 1 then algebraMap (ZMod 2) K (r 2)
      else algebraMap (ZMod 2) K (r 3))
    else if i = 1 then MvPolynomial.X 0 else
      if i = 2 then MvPolynomial.X 1 else MvPolynomial.X 2

set_option maxHeartbeats 1000000 in
theorem theta4HyperplaneCoordinates_degree_le
    {K : Type*} [Field K] [Algebra (ZMod 2) K] (r : Fin 4 → ZMod 2) :
    ∀ i, (theta4HyperplaneCoordinates (K := K) r i).totalDegree ≤ 1 := by
  classical
  intro i
  unfold theta4HyperplaneCoordinates
  split_ifs <;> first
    | exact totalDegree_theta4LinearForm_le_one (K := K) _
    | simp

theorem zmodTwo_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

theorem theta4_nonzero_over_field
    {K : Type*} [Field K] [Algebra (ZMod 2) K] :
    (theta4.map (algebraMap (ZMod 2) K)) ≠ 0 := by
  intro h
  have he := congrArg
    (MvPolynomial.eval (fun i : Fin 4 => if i = 0 then (1 : K) else 0)) h
  rw [MvPolynomial.eval_map] at he
  simp [theta4, k4X] at he

theorem mvPolynomial_zero_probability_bound
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : MvPolynomial (Fin 3) K) (hp : p ≠ 0)
    (S : Finset K) :
    (({x ∈ Fintype.piFinset (fun _ : Fin 3 => S) |
        MvPolynomial.eval x p = 0}.card : NNRat) /
        (S.card : NNRat)^3) ≤ (p.totalDegree : NNRat) / S.card := by
  exact MvPolynomial.schwartz_zippel_totalDegree hp S

#print axioms theta4_nonzero_over_field
#print axioms totalDegree_list_product_powers_le
#print axioms totalDegree_list_product_powers_le_of_linear
#print axioms totalDegree_list_sum_le
#print axioms theta4_eq_exponent_term_sum
#print axioms theta4_totalDegree_le
#print axioms theta4Pullback_totalDegree_le
#print axioms theta4ExponentTermPolyOver_eval
#print axioms eval_theta4ExponentTermPolyOver_list
#print axioms theta4Pullback_eval
#print axioms theta4Pullback_ne_zero_of_covering_hyperplane
#print axioms theta4_f2_hyperplane_has_nonzero_value
#print axioms theta4_eval_second_unit
#print axioms theta4_eval_first_two_units
#print axioms theta4_eval_first_unit_over_field
#print axioms theta4_eval_second_unit_over_field
#print axioms theta4_eval_first_two_units_over_field
#print axioms one_add_one_eq_zero_over_field
#print axioms theta4_field_hyperplane_has_nonzero_value
#print axioms mvPolynomial_zero_probability_bound

end Carlet
