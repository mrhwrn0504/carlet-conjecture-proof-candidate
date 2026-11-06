import Carlet.Theta5LastZeroCoefficientProbe
import Carlet.Theta5SparseSupportListsProbe
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic

noncomputable section
namespace Carlet

abbrev T5WordRing := MvPolynomial (Fin 5) (ZMod 2)

local instance t5WordRingCharTwo : CharP T5WordRing 2 :=
  charP_of_injective_algebraMap (by
    change Function.Injective (MvPolynomial.C : ZMod 2 →+* T5WordRing)
    exact MvPolynomial.C_injective _ _) 2

structure T5Exp4 where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr

def t5ExpPlus (e f : T5Exp4) : T5Exp4 :=
  ⟨e.a + f.a, e.b + f.b, e.c + f.c, e.d + f.d⟩

def t5ExpEmbed (e : T5Exp4) : Fin 5 →₀ ℕ :=
  Finsupp.single 0 e.a + Finsupp.single 1 e.b +
    Finsupp.single 2 e.c + Finsupp.single 3 e.d

lemma t5ExpEmbed_plus (e f : T5Exp4) :
    t5ExpEmbed (t5ExpPlus e f) = t5ExpEmbed e + t5ExpEmbed f := by
  ext i
  fin_cases i <;> simp [t5ExpEmbed, t5ExpPlus]

noncomputable def t5Atom (e : T5Exp4) : T5WordRing :=
  MvPolynomial.monomial (t5ExpEmbed e) 1

lemma t5Atom_plus (e f : T5Exp4) :
    t5Atom (t5ExpPlus e f) = t5Atom e * t5Atom f := by
  simp only [t5Atom, t5ExpEmbed_plus,
    MvPolynomial.monomial_mul, one_mul]

noncomputable def t5Denote : List T5Exp4 → T5WordRing
  | [] => 0
  | e :: es => t5Atom e + t5Denote es

lemma t5Denote_append (s t : List T5Exp4) :
    t5Denote (s ++ t) = t5Denote s + t5Denote t := by
  induction s with
  | nil => simp [t5Denote]
  | cons e s ih => simp only [List.cons_append, t5Denote, ih, add_assoc]

def t5Shift (e : T5Exp4) (s : List T5Exp4) : List T5Exp4 :=
  s.map (t5ExpPlus e)

def t5Times : List T5Exp4 → List T5Exp4 → List T5Exp4
  | [], _ => []
  | e :: s, t => t5Shift e t ++ t5Times s t

def t5Square (s : List T5Exp4) : List T5Exp4 :=
  s.map (fun e => t5ExpPlus e e)

lemma t5Denote_shift (e : T5Exp4) (s : List T5Exp4) :
    t5Denote (t5Shift e s) = t5Atom e * t5Denote s := by
  induction s with
  | nil => simp [t5Shift, t5Denote]
  | cons f s ih =>
      change t5Atom (t5ExpPlus e f) + t5Denote (t5Shift e s) =
        t5Atom e * (t5Atom f + t5Denote s)
      rw [t5Atom_plus, ih, mul_add]

lemma t5Denote_times (s t : List T5Exp4) :
    t5Denote (t5Times s t) = t5Denote s * t5Denote t := by
  induction s with
  | nil => simp [t5Times, t5Denote]
  | cons e s ih =>
      change t5Denote (t5Shift e t ++ t5Times s t) =
        (t5Atom e + t5Denote s) * t5Denote t
      rw [t5Denote_append, t5Denote_shift, ih, add_mul]

lemma t5SqAdd (p q : T5WordRing) : (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
  exact add_pow_char p q 2

lemma t5Denote_square (s : List T5Exp4) :
    t5Denote (t5Square s) = (t5Denote s) ^ 2 := by
  induction s with
  | nil => simp [t5Square, t5Denote]
  | cons e s ih =>
      change t5Atom (t5ExpPlus e e) + t5Denote (t5Square s) =
        (t5Atom e + t5Denote s) ^ 2
      rw [t5Atom_plus, ih, t5SqAdd]
      simp only [pow_two]

def t5v0 : List T5Exp4 := [⟨1, 0, 0, 0⟩]
def t5v1 : List T5Exp4 := [⟨0, 1, 0, 0⟩]
def t5v2 : List T5Exp4 := [⟨0, 0, 1, 0⟩]
def t5v3 : List T5Exp4 := [⟨0, 0, 0, 1⟩]

lemma t5Denote_v0 : t5Denote t5v0 = (MvPolynomial.X 0 : T5WordRing) := by
  simp [t5v0, t5Denote, t5Atom, t5ExpEmbed, MvPolynomial.X]

lemma t5Denote_v1 : t5Denote t5v1 = (MvPolynomial.X 1 : T5WordRing) := by
  simp [t5v1, t5Denote, t5Atom, t5ExpEmbed, MvPolynomial.X]

lemma t5Denote_v2 : t5Denote t5v2 = (MvPolynomial.X 2 : T5WordRing) := by
  simp [t5v2, t5Denote, t5Atom, t5ExpEmbed, MvPolynomial.X]

lemma t5Denote_v3 : t5Denote t5v3 = (MvPolynomial.X 3 : T5WordRing) := by
  simp [t5v3, t5Denote, t5Atom, t5ExpEmbed, MvPolynomial.X]

def t5ListT1 (s : List T5Exp4) : List T5Exp4 :=
  t5Square s ++ t5Times t5v0 s

def t5ListT2 (s : List T5Exp4) : List T5Exp4 :=
  t5Square (t5ListT1 s) ++ t5Times (t5ListT1 t5v1) (t5ListT1 s)

def t5ListT3 (s : List T5Exp4) : List T5Exp4 :=
  t5Square (t5ListT2 s) ++ t5Times (t5ListT2 t5v2) (t5ListT2 s)

def t5l2 : List T5Exp4 := t5Square t5v0 ++ t5ListT1 t5v1
def t5l4 : List T5Exp4 := t5Square t5l2 ++ t5ListT2 t5v2
def t5l8 : List T5Exp4 := t5Square t5l4 ++ t5ListT3 t5v3
def t5raw : List T5Exp4 := t5Square t5l8

lemma t5Denote_listT1 (s : List T5Exp4) :
    t5Denote (t5ListT1 s) =
      (t5Denote s)^2 + (MvPolynomial.X 0 : T5WordRing) * t5Denote s := by
  simp only [t5ListT1, t5Denote_append, t5Denote_square,
    t5Denote_times, t5Denote_v0]

lemma t5Denote_listT2 (s : List T5Exp4) :
    t5Denote (t5ListT2 s) =
      t5EvalValue2 (t5Denote s) := by
  simp only [t5ListT2, t5Denote_append, t5Denote_square,
    t5Denote_times, t5Denote_listT1, t5Denote_v1,
    t5EvalValue2, t5EvalValue1, t5EvalX]

lemma t5Denote_listT3 (s : List T5Exp4) :
    t5Denote (t5ListT3 s) =
      t5EvalValue3 (t5Denote s) := by
  simp only [t5ListT3, t5Denote_append, t5Denote_square,
    t5Denote_times, t5Denote_listT2, t5Denote_v2,
    t5EvalValue3, t5EvalX]

lemma t5Denote_l2 :
    t5Denote t5l2 = t5EvalP2.coeff 2 := by
  have heval : t5EvalP1.eval (t5EvalX 1) =
      (MvPolynomial.X 1 : T5WordRing)^2 +
        (MvPolynomial.X 0 : T5WordRing) * MvPolynomial.X 1 := by
    rw [t5EvalP1_value]
    rfl
  calc
    t5Denote t5l2 =
        (MvPolynomial.X 0 : T5WordRing)^2 +
          t5EvalP1.eval (t5EvalX 1) := by
      simp only [t5l2, t5Denote_append, t5Denote_square,
        t5Denote_v0, t5Denote_listT1, t5Denote_v1]
      rw [heval]
    _ = t5EvalP2.coeff 2 := t5Last_coeff2_P2.symm

lemma t5Denote_l4 :
    t5Denote t5l4 = t5EvalP3.coeff 4 := by
  simp only [t5l4, t5Denote_append, t5Denote_square,
    t5Denote_listT2, t5Denote_v2]
  rw [← t5EvalP2_value (MvPolynomial.X 2)]
  rw [t5Denote_l2]
  exact t5Last_coeff4_P3.symm

lemma t5Denote_l8 :
    t5Denote t5l8 = t5EvalP4.coeff 8 := by
  simp only [t5l8, t5Denote_append, t5Denote_square,
    t5Denote_listT3, t5Denote_v3]
  rw [← t5EvalP3_value (MvPolynomial.X 3)]
  rw [t5Denote_l4]
  exact t5Last_coeff8_P4.symm

lemma t5Denote_raw :
    t5Denote t5raw = (t5EvalP4.coeff 8)^2 := by
  rw [t5raw, t5Denote_square, t5Denote_l8]

def t5Toggle (e : T5Exp4) : List T5Exp4 → List T5Exp4
  | [] => [e]
  | f :: s => if e = f then s else f :: t5Toggle e s

def t5Normal : List T5Exp4 → List T5Exp4
  | [] => []
  | e :: s => t5Toggle e (t5Normal s)

def t5WordCoordinate (xs : List (Fin 5 × ℕ)) (i : Fin 5) : ℕ :=
  xs.foldr (fun p acc => (if p.1 = i then p.2 else 0) + acc) 0

lemma t5WordCoordinate_eq (xs : List (Fin 5 × ℕ)) (i : Fin 5) :
    t5WordCoordinate xs i = sparseXWordExponent xs i := by
  induction xs with
  | nil => simp [t5WordCoordinate, sparseXWordExponent]
  | cons p xs ih =>
      change (if p.1 = i then p.2 else 0) + t5WordCoordinate xs i =
        (Finsupp.single p.1 p.2 + sparseXWordExponent xs) i
      simp [Finsupp.single_apply, ih, eq_comm]

def t5ExpOfWord (xs : List (Fin 5 × ℕ)) : T5Exp4 :=
  ⟨t5WordCoordinate xs 0, t5WordCoordinate xs 1,
    t5WordCoordinate xs 2, t5WordCoordinate xs 3⟩

def t5Target : List T5Exp4 :=
  theta5LastZeroWordList.map (fun item => t5ExpOfWord item.1)

theorem t5Target_embedding_agrees :
    ∀ item ∈ theta5LastZeroWordList,
      t5ExpEmbed (t5ExpOfWord item.1) = sparseXWordExponent item.1 := by
  intro item h
  have h4 : t5WordCoordinate item.1 4 = 0 := by
    have hAll : ∀ item ∈ theta5LastZeroWordList,
        t5WordCoordinate item.1 4 = 0 := by decide
    exact hAll item h
  ext i
  fin_cases i
  · simp [t5ExpEmbed, t5ExpOfWord, t5WordCoordinate_eq]
  · simp [t5ExpEmbed, t5ExpOfWord, t5WordCoordinate_eq]
  · simp [t5ExpEmbed, t5ExpOfWord, t5WordCoordinate_eq]
  · simp [t5ExpEmbed, t5ExpOfWord, t5WordCoordinate_eq]
  · simp [t5ExpEmbed]
    rw [← t5WordCoordinate_eq item.1 4]
    exact h4.symm

theorem t5Target_weights_one :
    ∀ item ∈ theta5LastZeroWordList, item.2 = (1 : ZMod 2) := by
  decide

lemma t5Denote_mapWords (words : List (List (Fin 5 × ℕ) × ZMod 2))
    (hE : ∀ item ∈ words,
      t5ExpEmbed (t5ExpOfWord item.1) = sparseXWordExponent item.1)
    (hW : ∀ item ∈ words, item.2 = 1) :
    t5Denote (words.map (fun item => t5ExpOfWord item.1)) =
      sparseXWeightedWordsSum (R := ZMod 2) words := by
  induction words with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, t5Denote, sparseXWeightedWordsSum]
      have he := hE item (by simp)
      have hw := hW item (by simp)
      have ha : t5Atom (t5ExpOfWord item.1) = sparseXWord (R := ZMod 2) item.1 := by
        change MvPolynomial.monomial
          (t5ExpEmbed (t5ExpOfWord item.1)) (1 : ZMod 2) = _
        rw [sparseXWord_eq_monomial (R := ZMod 2), he]
      calc
        t5Atom (t5ExpOfWord item.1) +
            t5Denote (rest.map (fun item => t5ExpOfWord item.1)) =
            sparseXWord (R := ZMod 2) item.1 +
              t5Denote (rest.map (fun item => t5ExpOfWord item.1)) := by rw [ha]
        _ = sparseXWord (R := ZMod 2) item.1 * MvPolynomial.C item.2 +
            sparseXWeightedWordsSum (R := ZMod 2) rest := by
          rw [hw]
          simp only [MvPolynomial.C_1, mul_one]
          exact congrArg (fun p : T5WordRing => sparseXWord (R := ZMod 2) item.1 + p)
            (ih (by intro x hx; exact hE x (by simp [hx]))
              (by intro x hx; exact hW x (by simp [hx])))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
theorem t5FiniteWordCertificate :
    List.Perm (t5Normal t5raw) t5Target ∧
      t5Target.length = 35 ∧ t5Target.Nodup := by
  decide

lemma t5Denote_perm {s t : List T5Exp4} (h : List.Perm s t) :
    t5Denote s = t5Denote t := by
  induction h with
  | nil => rfl
  | cons e h ih => simpa [t5Denote] using congrArg (fun p => t5Atom e + p) ih
  | swap e f s => simp [t5Denote, add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma t5Denote_toggle (e : T5Exp4) (s : List T5Exp4) :
    t5Denote (t5Toggle e s) = t5Atom e + t5Denote s := by
  induction s with
  | nil => simp [t5Toggle, t5Denote]
  | cons f s ih =>
      by_cases h : e = f
      · subst f
        simp [t5Toggle]
        simp only [t5Denote]
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      · simp only [t5Toggle, if_neg h, t5Denote, ih]
        ac_rfl

lemma t5Denote_normal (s : List T5Exp4) :
    t5Denote (t5Normal s) = t5Denote s := by
  induction s with
  | nil => rfl
  | cons e s ih =>
      change t5Denote (t5Toggle e (t5Normal s)) = t5Atom e + t5Denote s
      rw [t5Denote_toggle, ih]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma t5Denote_target :
    t5Denote t5Target = theta5LastZero := by
  change t5Denote
      (theta5LastZeroWordList.map (fun item => t5ExpOfWord item.1)) = _
  calc
    t5Denote
        (theta5LastZeroWordList.map (fun item => t5ExpOfWord item.1)) =
        sparseXWeightedWordsSum (R := ZMod 2) theta5LastZeroWordList :=
      t5Denote_mapWords _ t5Target_embedding_agrees t5Target_weights_one
    _ = theta5LastZero := theta5LastZero_eq_weightedWordsSum.symm

theorem t5Last_eval_coeff8_squared_eq_theta5LastZero :
    (t5EvalP4.coeff 8)^2 = theta5LastZero := by
  calc
    (t5EvalP4.coeff 8)^2 = t5Denote t5raw := t5Denote_raw.symm
    _ = t5Denote (t5Normal t5raw) := (t5Denote_normal t5raw).symm
    _ = t5Denote t5Target := t5Denote_perm t5FiniteWordCertificate.1
    _ = theta5LastZero := t5Denote_target

theorem theta5_specialize_lastCoordinate_zero :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) T5WordRing)
      (fun i : Fin 5 => if i = 4 then (0 : T5WordRing) else MvPolynomial.X i)
      theta5 = theta5LastZero := by
  rw [theta5_eq_last_split]
  simp [theta5LastZero, theta5LastPositive, sparseXWord]

theorem t5Last_eval_coeff8_squared_eq_theta5_specialization :
    (t5EvalP4.coeff 8)^2 =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) T5WordRing)
        (fun i : Fin 5 => if i = 4 then (0 : T5WordRing) else MvPolynomial.X i)
        theta5 := by
  rw [theta5_specialize_lastCoordinate_zero]
  exact t5Last_eval_coeff8_squared_eq_theta5LastZero

#print axioms t5FiniteWordCertificate
#print axioms t5Last_eval_coeff8_squared_eq_theta5LastZero
#print axioms theta5_specialize_lastCoordinate_zero
#print axioms t5Last_eval_coeff8_squared_eq_theta5_specialization

end Carlet
