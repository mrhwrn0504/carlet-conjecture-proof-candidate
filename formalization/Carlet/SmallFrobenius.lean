import Carlet.Frobenius21
noncomputable section
open Polynomial
namespace Carlet

def smallL2 {R : Type*} [CommRing R] (x : R) : R := x^(2^2 : ℕ) + x^(2^1 : ℕ) + x
def smallL3 {R : Type*} [CommRing R] (x : R) : R := x^(2^3 : ℕ) + x^(2^1 : ℕ) + x

theorem smallL2_divides {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    smallL2 x ∣ x^(2^3 : ℕ) + x := by
  have h : (smallL2 x)^(2^1 : ℕ) + smallL2 x = x^(2^3 : ℕ) + x := by
    unfold smallL2
    simp only [add_pow_char_pow, ← pow_mul]
    ring_nf
    have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
    simp [htwo]
  rw [← h]
  exact dvd_add (dvd_pow_self (smallL2 x) (by norm_num)) (dvd_refl _)

theorem smallL3_divides {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    smallL3 x ∣ x^(2^7 : ℕ) + x := by
  have h : (smallL3 x)^(2^4 : ℕ) + (smallL3 x)^(2^2 : ℕ) +
      (smallL3 x)^(2^1 : ℕ) + smallL3 x = x^(2^7 : ℕ) + x := by
    unfold smallL3
    simp only [add_pow_char_pow, ← pow_mul]
    ring_nf
    have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
    simp [htwo]
  rw [← h]
  apply dvd_add
  apply dvd_add
  apply dvd_add
  all_goals first | exact dvd_refl _ | exact dvd_pow_self (smallL3 x) (by norm_num)

theorem smallL2_splits {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hc : Fintype.card K = 8) : (smallL2 (Polynomial.X : K[X])).Splits := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  apply split_of_card_divides
  rw [hc]
  exact smallL2_divides (Polynomial.X : K[X])

set_option maxRecDepth 4096 in
theorem smallL3_splits {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hc : Fintype.card K = 128) : (smallL3 (Polynomial.X : K[X])).Splits := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  apply split_of_card_divides
  rw [hc]
  exact smallL3_divides (Polynomial.X : K[X])

theorem smallL2_splits_of_three_dvd {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (n : ℕ) (hn : Module.finrank (ZMod 2) K = n) (hd : 3 ∣ n) :
    (smallL2 (Polynomial.X : K[X])).Splits := by
  classical
  let L := GaloisField 2 3
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 3 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 8 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
    norm_num
  have hd' : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by simpa [hr, hn]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd'
  have hs := (smallL2_splits (K := L) hc).map f.toRingHom
  simpa only [smallL2, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X] using hs

theorem smallL3_splits_of_seven_dvd {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (n : ℕ) (hn : Module.finrank (ZMod 2) K = n) (hd : 7 ∣ n) :
    (smallL3 (Polynomial.X : K[X])).Splits := by
  classical
  let L := GaloisField 2 7
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 7 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 128 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
    norm_num
  have hd' : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by simpa [hr, hn]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd'
  have hs := (smallL3_splits (K := L) hc).map f.toRingHom
  simpa only [smallL3, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X] using hs

theorem smallL_composition {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    smallL2 (smallL3 x) = linearizedP x ∧ smallL3 (smallL2 x) = linearizedP x := by
  constructor <;> unfold smallL2 smallL3 linearizedP <;>
    simp only [add_pow_char_pow, ← pow_mul] <;> ring_nf <;>
    have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2 <;> simp [htwo]

#print axioms smallL_composition
#print axioms smallL2_splits_of_three_dvd
#print axioms smallL3_splits_of_seven_dvd
#print axioms smallL2_splits
#print axioms smallL3_splits
#print axioms smallL2_divides
#print axioms smallL3_divides
end Carlet


