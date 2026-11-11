import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic
open Polynomial
abbrev F := ZMod 2
abbrev P := Polynomial F
example : (X^13 + (X^4 + (X^3 + (X + 1)) : P)).natDegree = 13 := by
  have h1 : ((X : P) + 1).natDegree ≤ 1 := by
    calc
      _ ≤ max (X : P).natDegree (1 : P).natDegree := Polynomial.natDegree_add_le _ _
      _ = 1 := by simp
  have h3 : ((X : P)^3 + (X + 1)).natDegree ≤ 3 := by
    calc
      _ ≤ max ((X : P)^3).natDegree (X + 1).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 3 := by simp only [Polynomial.natDegree_X_pow]; omega
  have h4 : ((X : P)^4 + (X^3 + (X + 1))).natDegree ≤ 4 := by
    calc
      _ ≤ max ((X : P)^4).natDegree (X^3 + (X + 1)).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 4 := by simp only [Polynomial.natDegree_X_pow]; omega
  have hs : ((X : P)^4 + (X^3 + (X + 1))).natDegree < 13 := by omega
  have hp : ((X : P)^13).natDegree = 13 := Polynomial.natDegree_X_pow 13
  have hs' : ((X : P)^4 + (X^3 + (X + 1))).natDegree < ((X : P)^13).natDegree := by rw [hp]; exact hs
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hs']
  exact hp
