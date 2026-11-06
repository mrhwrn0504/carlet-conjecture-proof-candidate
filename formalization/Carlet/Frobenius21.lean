import Carlet.SubfieldFive
noncomputable section
open Polynomial
namespace Carlet

def linearizedP {R : Type*} [CommRing R] (x : R) : R := x^(2^5 : ℕ) + x^(2^4 : ℕ) + x

def linearizedQ {R : Type*} [CommRing R] (y : R) : R :=
  y^(2^16 : ℕ) + y^(2^15 : ℕ) + y^(2^14 : ℕ) + y^(2^13 : ℕ) + y^(2^12 : ℕ) +
  y^(2^10 : ℕ) + y^(2^8 : ℕ) + y^(2^5 : ℕ) + y^(2^4 : ℕ) + y

theorem linearizedQ_dvd {R : Type*} [CommRing R] (y : R) : y ∣ linearizedQ y := by
  unfold linearizedQ
  repeat' apply dvd_add
  all_goals first | exact dvd_refl y | exact dvd_pow_self y (by norm_num)

theorem linearizedPQ {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    linearizedQ (linearizedP x) = x^(2^21 : ℕ) + x := by
  unfold linearizedP linearizedQ
  simp only [add_pow_char_pow, ← pow_mul]
  ring_nf
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simp [htwo]

theorem linearizedP_dvd {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    linearizedP x ∣ x^(2^21 : ℕ) + x := by
  rw [← linearizedPQ x]
  exact linearizedQ_dvd _

theorem split_of_card_divides {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (p : K[X]) (hdiv : p ∣ (X : K[X])^(Fintype.card K) + X) : p.Splits := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hs := FiniteField.splits_X_pow_card_sub_X 2 (K := K)
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at hs
  rw [CharTwo.sub_eq_add] at hs
  have hn := FiniteField.X_pow_card_sub_X_ne_zero K (Fintype.one_lt_card (α := K))
  rw [CharTwo.sub_eq_add] at hn
  exact hs.of_dvd hn hdiv

#print axioms split_of_card_divides
#print axioms linearizedP_dvd
end Carlet
