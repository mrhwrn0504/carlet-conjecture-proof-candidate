import Mathlib.Tactic

namespace Carlet

lemma zmodTwo_natCast_mod (n : ℕ) :
    (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq n 2).symm

example : (12 : ZMod 2) = 0 := by
  change ((12 : ℕ) : ZMod 2) = 0
  rw [zmodTwo_natCast_mod]
  norm_num

example {K : Type*} [Field K] [CharP K 2] (a b : K) (h : a+b=0) : a=b := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  linear_combination h + (-b)*h2

#print axioms zmodTwo_natCast_mod

end Carlet

