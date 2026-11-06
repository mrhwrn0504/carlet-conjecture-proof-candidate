import Carlet.AdditiveClosure
import Carlet.ImagePolynomial
import Carlet.KloostermanThree
import Carlet.SubfieldFive
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]

omit [DecidableEq K] in
/-- The two-dimensional base case for an even-degree field, obtained from its
    unique quadratic subfield. This is the `k=2` input used by the even-degree
    induction in Carlet--Hou, Theorem 5.2. -/
theorem hasZeroSumSubspace_two_of_even_degree (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (heven : Even n) :
    HasZeroSumSubspace K 2 := by
  classical
  let L := GaloisField 2 2
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 2 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 4 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
    norm_num
  obtain ⟨m, hm⟩ := heven
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    rw [hr, hn, hm]
    omega
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
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
    rw [Finset.card_univ, hc] at hcard
    have hsmall : ({0, 1} : Finset L).card ≤ 2 := by simp
    omega
  obtain ⟨a, ha0, ha1⟩ := ha
  simpa [hr] using embedded_finite_field_zero f a ha0 ha1

/-- The even-degree induction in Carlet--Hou, Theorem 5.2, once the 2- and
    3-dimensional base cases are established. The bases are explicit inputs. -/
theorem hasZeroSumSubspace_le_half_of_two_three
    (n : ℕ) (hn : Module.finrank (ZMod 2) K = n)
    (h2 : HasZeroSumSubspace K 2) (h3 : HasZeroSumSubspace K 3) :
    ∀ d : ℕ, 2 ≤ d → 2 * d ≤ n → HasZeroSumSubspace K d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd2 hhalf
    by_cases heven : Even d
    · rcases heven with ⟨r, hr⟩
      by_cases hdEq : d = 2
      · simpa [hdEq] using h2
      · have hdm : 2 ≤ d - 2 := by omega
        have hhalf' : 2 * (d - 2) ≤ n := by omega
        have hprev := ih (d - 2) (by omega) hdm hhalf'
        have hmul : (d - 2) * 2 < n := by omega
        have hadd := hasZeroSumSubspace_add (K := K) n (d - 2) 2 hn hmul hprev h2
        have heq : d - 2 + 2 = d := by omega
        simpa [heq] using hadd
    · have hdodd : Odd d := Nat.not_even_iff_odd.mp heven
      rcases hdodd with ⟨r, hr⟩
      by_cases hdEq : d = 3
      · simpa [hdEq] using h3
      · have hdm : 2 ≤ d - 2 := by omega
        have hhalf' : 2 * (d - 2) ≤ n := by omega
        have hprev := ih (d - 2) (by omega) hdm hhalf'
        have hmul : (d - 2) * 2 < n := by omega
        have hadd := hasZeroSumSubspace_add (K := K) n (d - 2) 2 hn hmul hprev h2
        have heq : d - 2 + 2 = d := by omega
        simpa [heq] using hadd

/-- Even-degree existence follows from the 2- and 3-dimensional bases.
    The dimension-extension and complementary-dimension steps are proved. -/
theorem evenDegreeCarlet_of_two_three_bases
    (n : ℕ) (_hnEven : Even n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hcard : Fintype.card K = 2 ^ n)
    (h2 : HasZeroSumSubspace K 2) (h3 : HasZeroSumSubspace K 3) :
    ∀ k : ℕ, 2 ≤ k → k + 2 ≤ n → HasZeroSumSubspace K k := by
  intro k hk hkmax
  classical
  have hn := finrank_eq_of_card (K := K) n hcard
  by_cases hlow : 2 * k ≤ n
  · exact hasZeroSumSubspace_le_half_of_two_three (K := K) n hn h2 h3 k hk hlow
  · have hother : 2 ≤ n - k := by omega
    have hotherhalf : 2 * (n - k) ≤ n := by omega
    have hbase := hasZeroSumSubspace_le_half_of_two_three (K := K) n hn h2 h3
      (n - k) hother hotherhalf
    have hiff := zeroSumSubspace_complement_of_card (K := K) n k hcard (by omega) (by omega)
    exact hiff.mpr hbase

/-- The even-degree theorem in Carlet--Hou, Theorem 5.2, reduced to its
    cited three-dimensional base case. The two-dimensional base is proved
    here, and the induction and complementary-dimension steps are internal. -/
theorem evenDegreeCarlet_of_three_base
    (n : ℕ) (hnEven : Even n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
    (hcard : Fintype.card K = 2 ^ n)
    (h3 : HasZeroSumSubspace K 3) :
    ∀ k : ℕ, 2 ≤ k → k + 2 ≤ n → HasZeroSumSubspace K k := by
  have hn := finrank_eq_of_card (K := K) n hcard
  exact evenDegreeCarlet_of_two_three_bases n hnEven K hcard
    (hasZeroSumSubspace_two_of_even_degree (K := K) n hn hnEven) h3

omit [DecidableEq K] in
/-- The cited three-dimensional base is immediate when the field contains its
    cubic subfield. This closes the even-degree family with 6 dividing n. -/
theorem hasZeroSumSubspace_three_of_three_dvd (n : ℕ)
    (hn : Module.finrank (ZMod 2) K = n) (hdiv : 3 ∣ n) :
    HasZeroSumSubspace K 3 := by
  classical
  let L := GaloisField 2 3
  let : Fintype L := Fintype.ofFinite L
  have hr : Module.finrank (ZMod 2) L = 3 := GaloisField.finrank 2 (by decide)
  have hc : Fintype.card L = 8 := by
    rw [← FiniteField.pow_finrank_eq_card 2 L, hr]
    norm_num
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, hn] using hdiv
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
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
    rw [Finset.card_univ, hc] at hcard
    have hsmall : ({0, 1} : Finset L).card ≤ 2 := by simp
    omega
  obtain ⟨a, ha0, ha1⟩ := ha
  simpa [hr] using embedded_finite_field_zero f a ha0 ha1

theorem evenDegreeCarlet_of_six_dvd
    (n : ℕ) (hnEven : Even n) (hdiv : 6 ∣ n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
    (hcard : Fintype.card K = 2 ^ n) :
    ∀ k : ℕ, 2 ≤ k → k + 2 ≤ n → HasZeroSumSubspace K k := by
  have hn := finrank_eq_of_card (K := K) n hcard
  have hdiv3 : 3 ∣ n := dvd_trans (by norm_num : 3 ∣ 6) hdiv
  exact evenDegreeCarlet_of_three_base n hnEven K hcard
    (hasZeroSumSubspace_three_of_three_dvd (K := K) n hn hdiv3)

/-- Full even-degree conclusion of Carlet--Hou, Theorem 5.2, for arbitrary
    finite fields of the stated cardinality. The k=3 base is proved here by
    the Kloosterman/Hasse argument, and k=2 handles the n=4 boundary. -/
theorem evenDegreeCarlet_unconditional
    (n : ℕ) (hnEven : Even n)
    (K : Type) [Field K] [Fintype K] [Algebra (ZMod 2) K] [DecidableEq K]
    (hcard : Fintype.card K = 2 ^ n) :
    ∀ k : ℕ, 2 ≤ k → k + 2 ≤ n → HasZeroSumSubspace K k := by
  intro k hk hkmax
  have hnlow : 4 ≤ n := by omega
  by_cases hn6 : 6 ≤ n
  · have hn := finrank_eq_of_card (K := K) n hcard
    exact evenDegreeCarlet_of_three_base n hnEven K hcard
      (hasZeroSumSubspace_three_even (K := K) n hn hnEven hn6) k hk hkmax
  · have hn4 : n = 4 := by
      rcases hnEven with ⟨m, hm⟩
      omega
    have hk2 : k = 2 := by omega
    subst k
    have hcard4 : Fintype.card K = 2 ^ 4 := by simpa [hn4] using hcard
    have hn' : Module.finrank (ZMod 2) K = 4 := finrank_eq_of_card (K := K) 4 hcard4
    have heven4 : Even 4 := by simpa [hn4] using hnEven
    exact hasZeroSumSubspace_two_of_even_degree (K := K) 4 hn' heven4

#print axioms hasZeroSumSubspace_le_half_of_two_three
#print axioms evenDegreeCarlet_of_two_three_bases
#print axioms hasZeroSumSubspace_two_of_even_degree
#print axioms evenDegreeCarlet_of_three_base
#print axioms hasZeroSumSubspace_three_of_three_dvd
#print axioms evenDegreeCarlet_of_six_dvd
#print axioms evenDegreeCarlet_unconditional
#print evenDegreeCarlet_unconditional

end Carlet



