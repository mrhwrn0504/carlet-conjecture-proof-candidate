import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic
namespace Carlet

lemma natCast_mod_two {R : Type*} [Semiring R] [CharP R 2] (n : Nat) :
    (n : R) = ((n % 2 : Nat) : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ih]
    have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases hz : n % 2 = 0
    · have hs : (n + 1) % 2 = 1 := by omega
      rw [hz, hs]
      norm_num
    · have ho : n % 2 = 1 := by omega
      have hs : (n + 1) % 2 = 0 := by omega
      rw [ho, hs]
      calc
        ((1 : Nat) : R) + 1 = ((2 : Nat) : R) := by norm_num
        _ = ((0 : Nat) : R) := CharP.cast_eq_zero R 2

lemma ofNat_mod_two {R : Type*} [Semiring R] [CharP R 2] (n : Nat) :
    (OfNat.ofNat n : R) = ((n % 2 : Nat) : R) := by
  change (n : R) = _
  exact natCast_mod_two n

example : (20 : MvPolynomial (Fin 4) (ZMod 2)) = 0 := by
  simp only [ofNat_mod_two, Nat.reduceMod]
end Carlet
