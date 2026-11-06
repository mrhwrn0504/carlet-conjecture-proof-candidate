import Carlet.SubfieldFive
import Carlet.TwoBaseReduction
noncomputable section
namespace Carlet

theorem hasZeroSumSubspace_of_dvd {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n d : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (hd2 : 2 ≤ d) (hdiv : d ∣ n) : HasZeroSumSubspace K d := by
  classical
  let L := GaloisField 2 d
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = d := GaloisField.finrank 2 (by omega)
  have hc : Fintype.card L = 2 ^ d := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
  have hc4 : 4 ≤ Fintype.card L := by
    rw [hc]
    exact le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by omega) hd2)
  have ha : ∃ a : L, a ≠ 0 ∧ a ≠ 1 := by
    by_contra h
    push Not at h
    have hs : (Finset.univ : Finset L) ⊆ {0, 1} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr (h x hx0)
    have hcard := Finset.card_le_card hs
    rw [Finset.card_univ] at hcard
    have hsmall : ({0, 1} : Finset L).card ≤ 2 := by simp
    omega
  obtain ⟨a, ha0, ha1⟩ := ha
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by simpa [hr, hn]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
  simpa [hr] using embedded_finite_field_zero f a ha0 ha1

theorem oddCarletConjecture_iff_four_and_five_coprime :
    OddCarletConjecture ↔
      (∀ (n k : ℕ), Odd n → (k = 4 ∨ k = 5 ∧ ¬ 5 ∣ n) → 2 * k + 1 ≤ n →
        ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K],
          Fintype.card K = 2 ^ n → HasZeroSumSubspace K k) := by
  classical
  constructor
  · intro h n k hn hk hbound K _ _ _ hcard
    apply h n k hn (by omega) (by omega) K hcard
  · intro h
    apply oddCarletConjecture_iff_four_and_five.mpr
    intro n k hn hk hbound K _ _ _ hcard
    rcases hk with hk | hk
    · exact h n k hn (Or.inl hk) hbound K hcard
    · by_cases hdiv : 5 ∣ n
      · subst k
        exact hasZeroSumSubspace_five_of_dvd n (finrank_eq_of_card n hcard) hdiv
      · exact h n k hn (Or.inr ⟨hk,hdiv⟩) hbound K hcard
#print axioms hasZeroSumSubspace_of_dvd
#print axioms oddCarletConjecture_iff_four_and_five_coprime
end Carlet
