import Carlet.Theta5RecurrenceWordCertificateProbe
import Carlet.Theta5PositiveSupportListsProbe

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic

noncomputable section
namespace Carlet

local instance t5PosRingCharTwo : CharP T5WordRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* T5WordRing)
    exact MvPolynomial.C_injective _ _) 2

structure T5Exp5 where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  deriving DecidableEq, Repr, Ord

def t5PosExpPlus (x y : T5Exp5) : T5Exp5 :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e⟩

def t5PosEmbed (x : T5Exp5) : Fin 5 →₀ ℕ :=
  Finsupp.single 0 x.a + Finsupp.single 1 x.b + Finsupp.single 2 x.c +
    Finsupp.single 3 x.d + Finsupp.single 4 x.e

lemma t5PosEmbed_plus (x y : T5Exp5) :
    t5PosEmbed (t5PosExpPlus x y) = t5PosEmbed x + t5PosEmbed y := by
  ext i
  fin_cases i <;> simp [t5PosEmbed, t5PosExpPlus]

noncomputable def t5PosAtom (x : T5Exp5) : T5WordRing :=
  MvPolynomial.monomial (t5PosEmbed x) 1

lemma t5PosAtom_plus (x y : T5Exp5) :
    t5PosAtom (t5PosExpPlus x y) = t5PosAtom x * t5PosAtom y := by
  simp only [t5PosAtom, t5PosEmbed_plus, MvPolynomial.monomial_mul, one_mul]

noncomputable def t5PosDenote : List T5Exp5 → T5WordRing
  | [] => 0
  | x :: xs => t5PosAtom x + t5PosDenote xs

lemma t5PosDenote_append (s t : List T5Exp5) :
    t5PosDenote (s ++ t) = t5PosDenote s + t5PosDenote t := by
  induction s with
  | nil => simp [t5PosDenote]
  | cons x s ih => simp only [List.cons_append, t5PosDenote, ih, add_assoc]

def t5PosShift (x : T5Exp5) (s : List T5Exp5) : List T5Exp5 :=
  s.map (t5PosExpPlus x)

def t5PosTimes : List T5Exp5 → List T5Exp5 → List T5Exp5
  | [], _ => []
  | x :: xs, ys => t5PosShift x ys ++ t5PosTimes xs ys

def t5PosSquare (s : List T5Exp5) : List T5Exp5 :=
  s.map (fun x => t5PosExpPlus x x)

lemma t5PosDenote_shift (x : T5Exp5) (s : List T5Exp5) :
    t5PosDenote (t5PosShift x s) = t5PosAtom x * t5PosDenote s := by
  induction s with
  | nil => simp [t5PosShift, t5PosDenote]
  | cons y s ih =>
      change t5PosAtom (t5PosExpPlus x y) + t5PosDenote (t5PosShift x s) =
        t5PosAtom x * (t5PosAtom y + t5PosDenote s)
      rw [t5PosAtom_plus, ih, mul_add]

lemma t5PosDenote_times (s t : List T5Exp5) :
    t5PosDenote (t5PosTimes s t) = t5PosDenote s * t5PosDenote t := by
  induction s with
  | nil => simp [t5PosTimes, t5PosDenote]
  | cons x s ih =>
      change t5PosDenote (t5PosShift x t ++ t5PosTimes s t) =
        (t5PosAtom x + t5PosDenote s) * t5PosDenote t
      rw [t5PosDenote_append, t5PosDenote_shift, ih, add_mul]

lemma t5PosSqAdd (p q : T5WordRing) : (p + q)^2 = p^2 + q^2 := by
  exact add_pow_char p q 2

lemma t5PosDenote_square (s : List T5Exp5) :
    t5PosDenote (t5PosSquare s) = (t5PosDenote s)^2 := by
  induction s with
  | nil => simp [t5PosSquare, t5PosDenote]
  | cons x s ih =>
      change t5PosAtom (t5PosExpPlus x x) + t5PosDenote (t5PosSquare s) =
        (t5PosAtom x + t5PosDenote s)^2
      rw [t5PosAtom_plus, ih, t5PosSqAdd]
      simp only [pow_two]

def t5PosV0 : List T5Exp5 := [⟨1, 0, 0, 0, 0⟩]
def t5PosV1 : List T5Exp5 := [⟨0, 1, 0, 0, 0⟩]
def t5PosV2 : List T5Exp5 := [⟨0, 0, 1, 0, 0⟩]
def t5PosV3 : List T5Exp5 := [⟨0, 0, 0, 1, 0⟩]
def t5PosV4 : List T5Exp5 := [⟨0, 0, 0, 0, 1⟩]

lemma t5PosDenote_v0 : t5PosDenote t5PosV0 = (MvPolynomial.X 0 : T5WordRing) := by
  simp [t5PosV0, t5PosDenote, t5PosAtom, t5PosEmbed, MvPolynomial.X]
lemma t5PosDenote_v1 : t5PosDenote t5PosV1 = (MvPolynomial.X 1 : T5WordRing) := by
  simp [t5PosV1, t5PosDenote, t5PosAtom, t5PosEmbed, MvPolynomial.X]
lemma t5PosDenote_v2 : t5PosDenote t5PosV2 = (MvPolynomial.X 2 : T5WordRing) := by
  simp [t5PosV2, t5PosDenote, t5PosAtom, t5PosEmbed, MvPolynomial.X]
lemma t5PosDenote_v3 : t5PosDenote t5PosV3 = (MvPolynomial.X 3 : T5WordRing) := by
  simp [t5PosV3, t5PosDenote, t5PosAtom, t5PosEmbed, MvPolynomial.X]
lemma t5PosDenote_v4 : t5PosDenote t5PosV4 = (MvPolynomial.X 4 : T5WordRing) := by
  simp [t5PosV4, t5PosDenote, t5PosAtom, t5PosEmbed, MvPolynomial.X]

def t5PosToggle (x : T5Exp5) : List T5Exp5 → List T5Exp5
  | [] => [x]
  | y :: ys => if x = y then ys else y :: t5PosToggle x ys

def t5PosNormal : List T5Exp5 → List T5Exp5
  | [] => []
  | x :: xs => t5PosToggle x (t5PosNormal xs)

lemma t5PosDenote_toggle (x : T5Exp5) (s : List T5Exp5) :
    t5PosDenote (t5PosToggle x s) = t5PosAtom x + t5PosDenote s := by
  induction s with
  | nil => simp [t5PosToggle, t5PosDenote]
  | cons y s ih =>
      by_cases h : x = y
      · subst y
        simp [t5PosToggle]
        simp only [t5PosDenote]
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      · simp only [t5PosToggle, if_neg h, t5PosDenote, ih]
        ac_rfl

lemma t5PosDenote_normal (s : List T5Exp5) :
    t5PosDenote (t5PosNormal s) = t5PosDenote s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
      change t5PosDenote (t5PosToggle x (t5PosNormal xs)) =
        t5PosAtom x + t5PosDenote xs
      rw [t5PosDenote_toggle, ih]

def t5PosListT1 (s : List T5Exp5) :=
  t5PosNormal (t5PosSquare s ++ t5PosTimes t5PosV0 s)
def t5PosListT2 (s : List T5Exp5) :=
  t5PosNormal
    (t5PosSquare (t5PosListT1 s) ++ t5PosTimes (t5PosListT1 t5PosV1) (t5PosListT1 s))
def t5PosListT3 (s : List T5Exp5) :=
  t5PosNormal
    (t5PosSquare (t5PosListT2 s) ++ t5PosTimes (t5PosListT2 t5PosV2) (t5PosListT2 s))
def t5PosListT4 (s : List T5Exp5) :=
  t5PosNormal
    (t5PosSquare (t5PosListT3 s) ++ t5PosTimes (t5PosListT3 t5PosV3) (t5PosListT3 s))

lemma t5PosDenote_listT1 (s : List T5Exp5) :
    t5PosDenote (t5PosListT1 s) = t5EvalValue1 (t5PosDenote s) := by
  rw [t5PosListT1, t5PosDenote_normal]
  simp only [t5PosDenote_append, t5PosDenote_square,
    t5PosDenote_times, t5PosDenote_v0, t5EvalValue1, t5EvalX]

lemma t5PosDenote_listT2 (s : List T5Exp5) :
    t5PosDenote (t5PosListT2 s) = t5EvalValue2 (t5PosDenote s) := by
  rw [t5PosListT2, t5PosDenote_normal]
  simp only [t5PosDenote_append, t5PosDenote_square,
    t5PosDenote_times, t5PosDenote_listT1, t5PosDenote_v1,
    t5EvalValue2, t5EvalValue1, t5EvalX]

lemma t5PosDenote_listT3 (s : List T5Exp5) :
    t5PosDenote (t5PosListT3 s) = t5EvalValue3 (t5PosDenote s) := by
  rw [t5PosListT3, t5PosDenote_normal]
  simp only [t5PosDenote_append, t5PosDenote_square,
    t5PosDenote_times, t5PosDenote_listT2, t5PosDenote_v2,
    t5EvalValue3, t5EvalX]

lemma t5PosDenote_listT4 (s : List T5Exp5) :
    t5PosDenote (t5PosListT4 s) = t5EvalValue4 (t5PosDenote s) := by
  rw [t5PosListT4, t5PosDenote_normal]
  simp only [t5PosDenote_append, t5PosDenote_square,
    t5PosDenote_times, t5PosDenote_listT3, t5PosDenote_v3,
    t5EvalValue4, t5EvalX]

def t5PosRaw : List T5Exp5 := t5PosListT4 t5PosV4

def t5PosWordExp (xs : List (Fin 5 × ℕ)) : T5Exp5 :=
  ⟨t5WordCoordinate xs 0, t5WordCoordinate xs 1,
    t5WordCoordinate xs 2, t5WordCoordinate xs 3, t5WordCoordinate xs 4⟩

def t5PosTarget : List T5Exp5 :=
  theta5LastPositiveWordList.map (fun item => t5PosWordExp item.1)

theorem t5PosTarget_embed_agrees :
    ∀ item ∈ theta5LastPositiveWordList,
      t5PosEmbed (t5PosWordExp item.1) = sparseXWordExponent item.1 := by
  intro item h
  ext i
  fin_cases i <;> simp [t5PosEmbed, t5PosWordExp, t5WordCoordinate_eq]

set_option maxRecDepth 4096 in
theorem t5PosTarget_weights_one :
    ∀ item ∈ theta5LastPositiveWordList, item.2 = (1 : ZMod 2) := by
  decide

lemma t5PosDenote_mapWords (words : List (List (Fin 5 × ℕ) × ZMod 2))
    (hE : ∀ item ∈ words,
      t5PosEmbed (t5PosWordExp item.1) = sparseXWordExponent item.1)
    (hW : ∀ item ∈ words, item.2 = 1) :
    t5PosDenote (words.map (fun item => t5PosWordExp item.1)) =
      sparseXWeightedWordsSum (R := ZMod 2) words := by
  induction words with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, t5PosDenote, sparseXWeightedWordsSum]
      have he := hE item (by simp)
      have hw := hW item (by simp)
      have ha : t5PosAtom (t5PosWordExp item.1) = sparseXWord (R := ZMod 2) item.1 := by
        change MvPolynomial.monomial
          (t5PosEmbed (t5PosWordExp item.1)) (1 : ZMod 2) = _
        rw [sparseXWord_eq_monomial (R := ZMod 2), he]
      calc
        t5PosAtom (t5PosWordExp item.1) +
            t5PosDenote (rest.map (fun item => t5PosWordExp item.1)) =
            sparseXWord (R := ZMod 2) item.1 +
              t5PosDenote (rest.map (fun item => t5PosWordExp item.1)) := by rw [ha]
        _ = sparseXWord (R := ZMod 2) item.1 * MvPolynomial.C item.2 +
            sparseXWeightedWordsSum (R := ZMod 2) rest := by
          rw [hw]
          simp only [MvPolynomial.C_1, mul_one]
          exact congrArg (fun p : T5WordRing => sparseXWord (R := ZMod 2) item.1 + p)
            (ih (by intro x hx; exact hE x (by simp [hx]))
              (by intro x hx; exact hW x (by simp [hx])))

lemma t5PosDenote_target : t5PosDenote t5PosTarget = theta5LastPositive := by
  change t5PosDenote
      (theta5LastPositiveWordList.map (fun item => t5PosWordExp item.1)) = _
  calc
    t5PosDenote
        (theta5LastPositiveWordList.map (fun item => t5PosWordExp item.1)) =
        sparseXWeightedWordsSum (R := ZMod 2) theta5LastPositiveWordList :=
      t5PosDenote_mapWords _ t5PosTarget_embed_agrees t5PosTarget_weights_one
    _ = theta5LastPositive := theta5LastPositive_eq_weightedWordsSum.symm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 30000000 in
theorem t5PosNormalizedWordCertificate :
    t5PosRaw = t5PosTarget := by
  decide

theorem t5PosFiniteWordCertificate :
    t5PosRaw = t5PosTarget ∧
      t5PosTarget.length = 150 := by
  exact ⟨t5PosNormalizedWordCertificate, by
    simp [t5PosTarget, theta5LastPositiveWordList_length]⟩

theorem t5P4_eval_x4_eq_theta5LastPositive :
    t5EvalP4.eval (t5EvalX 4) = theta5LastPositive := by
  calc
    t5EvalP4.eval (t5EvalX 4) = t5PosDenote t5PosRaw := by
      rw [t5EvalP4_value]
      simp [t5EvalX, t5PosRaw, t5PosDenote_listT4, t5PosDenote_v4]
    _ = t5PosDenote t5PosTarget := by rw [t5PosFiniteWordCertificate.1]
    _ = theta5LastPositive := t5PosDenote_target

theorem theta5_eq_coeff8_sq_add_eval :
    theta5 = (t5EvalP4.coeff 8)^2 + t5EvalP4.eval (t5EvalX 4) := by
  rw [theta5_eq_last_split, t5Last_eval_coeff8_squared_eq_theta5LastZero,
    t5P4_eval_x4_eq_theta5LastPositive]

#print axioms t5PosFiniteWordCertificate
#print axioms t5PosNormalizedWordCertificate
#print axioms t5P4_eval_x4_eq_theta5LastPositive
#print axioms theta5_eq_coeff8_sq_add_eval

end Carlet
