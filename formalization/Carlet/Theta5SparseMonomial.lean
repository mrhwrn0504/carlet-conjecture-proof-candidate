import Mathlib.Algebra.MvPolynomial.Basic

namespace Carlet

open MvPolynomial

variable {R : Type*} [CommSemiring R] [DecidableEq (Fin 5)]

omit [DecidableEq (Fin 5)] in
/-- A Frobenius-coordinate monomial is a single supported exponent vector. -/
theorem mv_X_pow_eq_monomial_single (i : Fin 5) (k : ℕ) :
    (MvPolynomial.X i : MvPolynomial (Fin 5) R) ^ k =
      MvPolynomial.monomial (Finsupp.single i k) 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    change MvPolynomial.monomial (Finsupp.single i k) 1 *
      MvPolynomial.monomial (Finsupp.single i 1) 1 = _
    rw [MvPolynomial.monomial_mul, ← Finsupp.single_add]
    simp

/-- Coefficient extraction from a product of two Frobenius-coordinate
    monomials reduces to equality of exponent vectors. -/
theorem mv_coeff_X_pow_mul_X_pow (i j : Fin 5) (a b : ℕ)
    (e : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff e
        ((MvPolynomial.X i : MvPolynomial (Fin 5) R) ^ a *
          MvPolynomial.X j ^ b) =
      if Finsupp.single i a + Finsupp.single j b = e then 1 else 0 := by
  rw [mv_X_pow_eq_monomial_single, mv_X_pow_eq_monomial_single,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial]
  simp

/-- The same coefficient formula with a pre-assembled sparse monomial on the
    right; this is the induction step for products of three or more powers. -/
theorem mv_coeff_X_pow_mul_monomial (i : Fin 5) (a : ℕ)
    (s e : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff e
        ((MvPolynomial.X i : MvPolynomial (Fin 5) R) ^ a *
          MvPolynomial.monomial s 1) =
      if Finsupp.single i a + s = e then 1 else 0 := by
  rw [mv_X_pow_eq_monomial_single, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_monomial]
  simp

omit [DecidableEq (Fin 5)] in
/-- Multiplication of one Frobenius-coordinate monomial by a sparse monomial
    adds their exponent vectors without expanding terms. -/
theorem mv_X_pow_mul_monomial (i : Fin 5) (a : ℕ)
    (s : Fin 5 →₀ ℕ) :
    (MvPolynomial.X i : MvPolynomial (Fin 5) R) ^ a *
        MvPolynomial.monomial s 1 =
      MvPolynomial.monomial (Finsupp.single i a + s) 1 := by
  rw [mv_X_pow_eq_monomial_single, MvPolynomial.monomial_mul]
  simp

/-- Sparse polynomial product encoded by a finite word of variable powers. -/
noncomputable def sparseXWord : List (Fin 5 × ℕ) → MvPolynomial (Fin 5) R
  | [] => 1
  | (i, a) :: xs => MvPolynomial.X i ^ a * sparseXWord xs

/-- The exponent vector represented by `sparseXWord`. -/
noncomputable def sparseXWordExponent : List (Fin 5 × ℕ) → Fin 5 →₀ ℕ
  | [] => 0
  | (i, a) :: xs => Finsupp.single i a + sparseXWordExponent xs

omit [DecidableEq (Fin 5)] in
/-- Every finite word of Frobenius-coordinate powers is one sparse monomial. -/
theorem sparseXWord_eq_monomial (xs : List (Fin 5 × ℕ)) :
    sparseXWord (R := R) xs =
      MvPolynomial.monomial (sparseXWordExponent xs) 1 := by
  induction xs with
  | nil => simp [sparseXWord, sparseXWordExponent]
  | cons x xs ih =>
    rcases x with ⟨i, a⟩
    simp only [sparseXWord, sparseXWordExponent]
    rw [ih, mv_X_pow_mul_monomial]

/-- Coefficients of a sparse word are a single exponent-vector test. -/
theorem coeff_sparseXWord (xs : List (Fin 5 × ℕ))
    (e : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff e (sparseXWord (R := R) xs) =
      if sparseXWordExponent xs = e then 1 else 0 := by
  rw [sparseXWord_eq_monomial, MvPolynomial.coeff_monomial]

/-- Coefficients of a sparse word multiplied by a scalar are a single
    exponent-vector test weighted by that scalar. -/
theorem coeff_sparseXWord_mul_C (xs : List (Fin 5 × ℕ)) (a : R)
    (e : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff e (sparseXWord (R := R) xs * MvPolynomial.C a) =
      if sparseXWordExponent xs = e then a else 0 := by
  rw [mul_comm (sparseXWord (R := R) xs) (MvPolynomial.C a),
    sparseXWord_eq_monomial, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_monomial]
  simp
/-- Sum a finite list of scalar-weighted sparse Frobenius monomials. -/
noncomputable def sparseXWeightedWordsSum :
    List (List (Fin 5 × ℕ) × R) → MvPolynomial (Fin 5) R
  | [] => 0
  | (xs, a) :: rest =>
      sparseXWord (R := R) xs * MvPolynomial.C a + sparseXWeightedWordsSum rest

/-- The coefficient of a finite sparse-word sum is the matching finite sum of
    exponent-vector tests, without materializing a large `MvPolynomial` normal form. -/
theorem coeff_sparseXWeightedWordsSum
    (words : List (List (Fin 5 × ℕ) × R)) (e : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff e (sparseXWeightedWordsSum (R := R) words) =
      words.foldr (fun item acc =>
        (if sparseXWordExponent item.1 = e then item.2 else 0) + acc) 0 := by
  induction words with
  | nil => simp [sparseXWeightedWordsSum]
  | cons item rest ih =>
    rcases item with ⟨xs, a⟩
    simp [sparseXWeightedWordsSum, coeff_sparseXWord_mul_C, ih]
#print axioms mv_X_pow_eq_monomial_single
#print axioms mv_coeff_X_pow_mul_X_pow
#print axioms mv_coeff_X_pow_mul_monomial
#print axioms mv_X_pow_mul_monomial
#print axioms sparseXWord_eq_monomial
#print axioms coeff_sparseXWord
#print axioms coeff_sparseXWord_mul_C
#print axioms coeff_sparseXWeightedWordsSum

end Carlet


