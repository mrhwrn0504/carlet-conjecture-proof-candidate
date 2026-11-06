import Carlet.Theta5PositiveSupportListsProbe
import Carlet.Theta5SparseSupportListsProbe
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {σ R : Type*} [CommSemiring R] [Algebra (ZMod 2) R]

def theta5SubstHom (f : Fin 5 → MvPolynomial σ R) :
    MvPolynomial (Fin 5) (ZMod 2) →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : R →+* MvPolynomial σ R).comp (algebraMap (ZMod 2) R)) f

def theta5WordOver (f : Fin 5 → MvPolynomial σ R) :
    List (Fin 5 × ℕ) → MvPolynomial σ R
  | [] => 1
  | (i, e) :: rest => f i ^ e * theta5WordOver f rest

def theta5WordsOver (f : Fin 5 → MvPolynomial σ R) :
    List (List (Fin 5 × ℕ) × ZMod 2) → MvPolynomial σ R
  | [] => 0
  | (word, c) :: rest =>
      theta5WordOver f word * MvPolynomial.C (algebraMap (ZMod 2) R c) +
        theta5WordsOver f rest

theorem theta5Subst_sparseWord (f : Fin 5 → MvPolynomial σ R)
    (word : List (Fin 5 × ℕ)) :
    theta5SubstHom f (sparseXWord (R := ZMod 2) word) = theta5WordOver f word := by
  induction word with
  | nil => simp [sparseXWord, theta5WordOver]
  | cons item rest ih =>
    rcases item with ⟨i, e⟩
    simp only [sparseXWord, theta5WordOver, map_mul, map_pow, ih]
    simp [theta5SubstHom]

theorem theta5Subst_weightedWords (f : Fin 5 → MvPolynomial σ R)
    (words : List (List (Fin 5 × ℕ) × ZMod 2)) :
    theta5SubstHom f (sparseXWeightedWordsSum (R := ZMod 2) words) =
      theta5WordsOver f words := by
  induction words with
  | nil => simp [sparseXWeightedWordsSum, theta5WordsOver]
  | cons item rest ih =>
    rcases item with ⟨word, c⟩
    simp only [sparseXWeightedWordsSum, theta5WordsOver, map_add, map_mul,
      theta5Subst_sparseWord, ih]
    simp [theta5SubstHom]

omit [Algebra (ZMod 2) R] in
theorem theta5WordOver_totalDegree_le (f : Fin 5 → MvPolynomial σ R)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (word : List (Fin 5 × ℕ)) :
    (theta5WordOver f word).totalDegree ≤ (word.map Prod.snd).sum := by
  induction word with
  | nil => simp [theta5WordOver]
  | cons item rest ih =>
    rcases item with ⟨i, e⟩
    simp only [theta5WordOver, List.map_cons, List.sum_cons]
    calc
      (f i ^ e * theta5WordOver f rest).totalDegree ≤
          (f i ^ e).totalDegree + (theta5WordOver f rest).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ e * (f i).totalDegree + (rest.map Prod.snd).sum :=
        Nat.add_le_add (MvPolynomial.totalDegree_pow _ _) ih
      _ ≤ e + (rest.map Prod.snd).sum := by
        exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_left e (hf i)) _

theorem theta5WordsOver_totalDegree_le (f : Fin 5 → MvPolynomial σ R)
    (hf : ∀ i, (f i).totalDegree ≤ 1)
    (words : List (List (Fin 5 × ℕ) × ZMod 2)) (d : ℕ)
    (hw : ∀ item ∈ words, (item.1.map Prod.snd).sum ≤ d) :
    (theta5WordsOver f words).totalDegree ≤ d := by
  induction words with
  | nil => simp [theta5WordsOver]
  | cons item rest ih =>
    rcases item with ⟨word, c⟩
    have hword : (word.map Prod.snd).sum ≤ d := hw (word, c) (by simp)
    have hrest : ∀ item ∈ rest, (item.1.map Prod.snd).sum ≤ d := by
      intro item hi
      exact hw item (by simp [hi])
    have hterm :
        (theta5WordOver f word * MvPolynomial.C (algebraMap (ZMod 2) R c)).totalDegree ≤ d := by
      calc
        _ ≤ (theta5WordOver f word).totalDegree +
            (MvPolynomial.C (algebraMap (ZMod 2) R c) : MvPolynomial σ R).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ (word.map Prod.snd).sum := by simpa using theta5WordOver_totalDegree_le f hf word
        _ ≤ d := hword
    change (theta5WordOver f word * MvPolynomial.C (algebraMap (ZMod 2) R c) +
      theta5WordsOver f rest).totalDegree ≤ d
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le hterm (ih hrest))

set_option maxRecDepth 8192 in
theorem theta5_zeroWord_weights :
    ∀ item ∈ theta5LastZeroWordList, (item.1.map Prod.snd).sum ≤ 16 := by
  have h : theta5LastZeroWordList.all
      (fun item => decide ((item.1.map Prod.snd).sum ≤ 16)) = true := by decide
  intro item hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) item hi)

set_option maxRecDepth 8192 in
theorem theta5_positiveWord_weights :
    ∀ item ∈ theta5LastPositiveWordList, (item.1.map Prod.snd).sum ≤ 16 := by
  have h : theta5LastPositiveWordList.all
      (fun item => decide ((item.1.map Prod.snd).sum ≤ 16)) = true := by decide
  intro item hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) item hi)

/-- Any linear substitution into the explicit Θ₅ preserves the degree-16
    upper bound. It is the degree hypothesis for hyperplane zero counting. -/
theorem theta5_linear_substitution_totalDegree_le (f : Fin 5 → MvPolynomial σ R)
    (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (theta5SubstHom f theta5).totalDegree ≤ 16 := by
  rw [theta5_eq_last_split, theta5LastZero_eq_weightedWordsSum,
    theta5LastPositive_eq_weightedWordsSum, map_add,
    theta5Subst_weightedWords, theta5Subst_weightedWords]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (theta5WordsOver_totalDegree_le f hf _ 16 theta5_zeroWord_weights)
      (theta5WordsOver_totalDegree_le f hf _ 16 theta5_positiveWord_weights))

#print axioms theta5_linear_substitution_totalDegree_le
end Carlet
