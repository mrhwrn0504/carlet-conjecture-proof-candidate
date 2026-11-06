import Carlet.CoordinateCongruence

noncomputable section

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

def extendVector {r : ℕ} (x : Fin r → A) (j : ℕ) : A :=
  if h : j < r then x ⟨j, h⟩ else 0

@[simp] theorem extendVector_apply {r : ℕ} (x : Fin r → A) (j : Fin r) :
    extendVector x j.val = x j := by simp [extendVector, j.isLt]

/-- Exactly the manuscript's free coordinates: binom(r,2) entries of u,
and r-1 entries each of c,t,d. Diagonal and first coordinates are fixed. -/
@[ext] structure QuadraticCoordinates (A : Type*) (r : ℕ) where
  c : Fin (r-1) → A
  t : Fin (r-1) → A
  d : Fin (r-1) → A
  u : (a : Fin r) → Fin a.val → A

def cSeq {r : ℕ} (y : QuadraticCoordinates A r) (j : ℕ) : A :=
  if h : j < r-1 then y.c ⟨j,h⟩ else 0

def tSeq {r : ℕ} (y : QuadraticCoordinates A r) (j : ℕ) : A :=
  if j = 0 then 1 else if h : j-1 < r-1 then y.t ⟨j-1,h⟩ else 0

def dSeq {r : ℕ} (y : QuadraticCoordinates A r) (j : ℕ) : A :=
  if j = 0 then 1 else if h : j-1 < r-1 then y.d ⟨j-1,h⟩ else 0

def uSeq {r : ℕ} (y : QuadraticCoordinates A r) (a j : ℕ) : A :=
  if ha : a < r then
    if hj : j < a then y.u ⟨a,ha⟩ ⟨j,hj⟩ else if j = a then 1 else 0
  else 0

@[simp] theorem cSeq_apply {r : ℕ} (y : QuadraticCoordinates A r) (j : Fin (r-1)) :
    cSeq y j.val = y.c j := by simp [cSeq, j.isLt]

@[simp] theorem tSeq_apply {r : ℕ} (y : QuadraticCoordinates A r) (j : Fin (r-1)) :
    tSeq y (j.val+1) = y.t j := by simp [tSeq, j.isLt]

@[simp] theorem dSeq_apply {r : ℕ} (y : QuadraticCoordinates A r) (j : Fin (r-1)) :
    dSeq y (j.val+1) = y.d j := by simp [dSeq, j.isLt]

@[simp] theorem uSeq_apply {r : ℕ} (y : QuadraticCoordinates A r) (a : Fin r) (j : Fin a.val) :
    uSeq y a.val j.val = y.u a j := by simp [uSeq, a.isLt, j.isLt]

def rawForward (x : ℕ → A) (r : ℕ) : QuadraticCoordinates A r where
  c := fun j => forwardC x j.val
  t := fun j => forwardT x (j.val+1)
  d := fun j => forwardD x (j.val+1)
  u := fun a j => forwardU x a.val j.val

theorem cSeq_rawForward (x : ℕ → A) (r j : ℕ) (hj : j+1 < r) :
    cSeq (rawForward x r) j = forwardC x j := by
  simp [cSeq, rawForward, show j < r-1 by omega]

theorem tSeq_rawForward (x : ℕ → A) (r j : ℕ) (hj : j < r) :
    tSeq (rawForward x r) j = forwardT x j := by
  by_cases h0 : j = 0
  · subst j; simp [tSeq, forwardT_zero]
  · have hsub : j-1+1 = j := by omega
    simp [tSeq, rawForward, h0, show j-1 < r-1 by omega, hsub]

theorem dSeq_rawForward (x : ℕ → A) (r j : ℕ) (hj : j < r) :
    dSeq (rawForward x r) j = forwardD x j := by
  by_cases h0 : j = 0
  · subst j; simp [dSeq, forwardD, forwardT_zero]
  · have hsub : j-1+1 = j := by omega
    simp [dSeq, rawForward, h0, show j-1 < r-1 by omega, hsub]

theorem uSeq_rawForward (h2 : (2 : A) = 0) (x : ℕ → A) (r a j : ℕ)
    (h : FullRank x r) (ha : a < r) (hj : j ≤ a) :
    uSeq (rawForward x r) a j = forwardU x a j := by
  by_cases hlt : j < a
  · simp [uSeq, rawForward, ha, hlt]
  · have he : j = a := by omega
    subst j
    simp only [uSeq, ha, dite_true, Nat.lt_irrefl, dite_false, ite_true]
    exact (forwardU_diagonal h2 x r a ha h).symm

def OpenCarletPoint (A : Type*) [CommRing A] (r : ℕ) :=
  {x : Fin r → A // OpenCarletCondition (extendVector x) r}

def QuadraticPoint (A : Type*) [CommRing A] (r : ℕ) :=
  {y : QuadraticCoordinates A r // QuadraticCondition (cSeq y) (tSeq y) (dSeq y) (uSeq y) r}

theorem rawForward_condition [Algebra (ZMod 2) A] (x : ℕ → A) (r : ℕ) (hr : 0 < r)
    (h : OpenCarletCondition x r) :
    QuadraticCondition (cSeq (rawForward x r)) (tSeq (rawForward x r))
      (dSeq (rawForward x r)) (uSeq (rawForward x r)) r := by
  apply quadraticCondition_transfer (forwardC x) (forwardT x) (forwardD x)
    (cSeq (rawForward x r)) (tSeq (rawForward x r)) (dSeq (rawForward x r))
    (forwardU x) (uSeq (rawForward x r)) r hr
  · intro j hj; exact (cSeq_rawForward x r j hj).symm
  · intro j hj; exact (tSeq_rawForward x r j hj).symm
  · intro j hj; exact (dSeq_rawForward x r j hj).symm
  · intro a ha j hj; exact (uSeq_rawForward algebra_two_eq_zero x r a j h.2.1 ha hj).symm
  · exact forward_satisfies_quadratic x r h

def finiteForward [Algebra (ZMod 2) A] (r : ℕ) (hr : 0 < r)
    (x : OpenCarletPoint A r) : QuadraticPoint A r :=
  ⟨rawForward (extendVector x.val) r, rawForward_condition _ r hr x.property⟩

def reverseVector {r : ℕ} (y : QuadraticCoordinates A r) : Fin r → A :=
  fun a => uSeq y a.val 0

theorem extend_reverseVector {r : ℕ} (y : QuadraticCoordinates A r) :
    extendVector (reverseVector y) = fun j => uSeq y j 0 := by
  funext j
  by_cases hj : j < r
  · simp [extendVector, reverseVector, hj]
  · simp [extendVector, uSeq, hj]

def finiteReverse [Algebra (ZMod 2) A] (r : ℕ) (hr : 0 < r)
    (y : QuadraticPoint A r) : OpenCarletPoint A r := by
  refine ⟨reverseVector y.val, ?_⟩
  rw [extend_reverseVector]
  obtain ⟨hu, ht0, ht, hc, hsum⟩ := y.property
  exact reverse_satisfies_openCarlet _ _ _ _ r hr hu ht0 ht hc hsum

theorem finite_left_inverse [Algebra (ZMod 2) A] (r : ℕ) (hr : 0 < r)
    (x : OpenCarletPoint A r) : finiteReverse r hr (finiteForward r hr x) = x := by
  apply Subtype.ext
  funext a
  change uSeq (rawForward (extendVector x.val) r) a.val 0 = x.val a
  rw [uSeq_rawForward algebra_two_eq_zero _ r a.val 0 x.property.2.1 a.isLt (Nat.zero_le _),
    forwardU_zero _ x.property.1, extendVector_apply]

theorem finite_right_inverse [Algebra (ZMod 2) A] (r : ℕ) (hr : 0 < r)
    (y : QuadraticPoint A r) : finiteForward r hr (finiteReverse r hr y) = y := by
  apply Subtype.ext
  apply QuadraticCoordinates.ext
  · funext j
    change forwardC (extendVector (reverseVector y.val)) j.val = y.val.c j
    rw [extend_reverseVector, reverse_then_forward_c algebra_two_eq_zero
      (cSeq y.val) (tSeq y.val) (dSeq y.val) (uSeq y.val) r j.val (by omega) y.property,
      cSeq_apply]
  · funext j
    change forwardT (extendVector (reverseVector y.val)) (j.val+1) = y.val.t j
    rw [extend_reverseVector, reverse_then_forward_t
      (cSeq y.val) (tSeq y.val) (dSeq y.val) (uSeq y.val) r hr y.property (j.val+1) (by omega),
      tSeq_apply]
  · funext j
    change forwardD (extendVector (reverseVector y.val)) (j.val+1) = y.val.d j
    rw [extend_reverseVector, reverse_then_forward_d
      (cSeq y.val) (tSeq y.val) (dSeq y.val) (uSeq y.val) r hr y.property (j.val+1) (by omega),
      dSeq_apply]
  · funext a j
    change forwardU (extendVector (reverseVector y.val)) a.val j.val = y.val.u a j
    rw [extend_reverseVector, reverse_then_forward_u
      (cSeq y.val) (tSeq y.val) (dSeq y.val) (uSeq y.val) r a.val j.val y.property a.isLt (by omega),
      uSeq_apply]

/-- A genuine equivalence of the finite coordinate solution sets over
every F₂-algebra. Scheme representability and naturality are separate obligations. -/
def finiteCoordinateEquiv [Algebra (ZMod 2) A] (r : ℕ) (hr : 0 < r) :
    OpenCarletPoint A r ≃ QuadraticPoint A r where
  toFun := finiteForward r hr
  invFun := finiteReverse r hr
  left_inv := finite_left_inverse r hr
  right_inv := finite_right_inverse r hr

#print axioms finite_left_inverse
#print axioms finite_right_inverse
#print axioms finiteCoordinateEquiv

end Carlet.Quadratic
