import Carlet.K4NormOneThetaBridgeProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K] [DecidableEq K]

attribute [local instance] Classical.propDecidable
local instance (E : Submodule (ZMod 2) K) : Fintype E := Fintype.ofFinite E

omit [DecidableEq K] in
theorem k5GeneralTraceGood_card_filter (E : Submodule (ZMod 2) K) :
    (∑ p : k4NormOnePairs (K := K),
      if k4GeneralTraceGood E p then (64 : ℝ) else 0) =
      (Fintype.card {p : k4NormOnePairs (K := K) // k4GeneralTraceGood E p} : ℝ) * 64 := by
  classical
  let P : k4NormOnePairs (K := K) → Prop := fun p => k4GeneralTraceGood E p
  let s : Finset (k4NormOnePairs (K := K)) := Finset.univ.filter P
  calc
    _ = ∑ p ∈ s, (64 : ℝ) := by
      simpa [s, P] using
        (Fintype.sum_ite_mem s (fun _ : k4NormOnePairs (K := K) => (64 : ℝ)))
    _ = (s.card : ℝ) * 64 := by simp
    _ = (Fintype.card {p : k4NormOnePairs (K := K) // P p} : ℝ) * 64 := by
      have hc : Fintype.card {p : k4NormOnePairs (K := K) // P p} = s.card := by
        simpa [s, P] using (Fintype.card_subtype P)
      rw [← hc]

omit [DecidableEq K] in
theorem k5GeneralTraceGood_card_fourier_sum (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K = n)
    (E : Submodule (ZMod 2) K) (hcard : Fintype.card E = 8) :
    (Fintype.card {p : k4NormOnePairs (K := K) // k4GeneralTraceGood E p} : ℝ) * 64 =
      ∑ r : E, ∑ s : E, k4ASWFourierCoefficient (s : K) (r : K) := by
  calc
    _ = ∑ p : k4NormOnePairs (K := K),
        if k4GeneralTraceGood E p then (64 : ℝ) else 0 :=
      (k5GeneralTraceGood_card_filter E).symm
    _ = ∑ p : k4NormOnePairs (K := K),
        (∑ r : E, traceCharacter ((r : K) * p.val.2)) *
        (∑ s : E, traceCharacter ((s : K) * (p.val.1 + p.val.2))) := by
      apply Fintype.sum_congr
      intro p
      by_cases hg : k4GeneralTraceGood E p
      · have hc : (∀ a ∈ E, Algebra.trace (ZMod 2) K (a * p.val.2) = 0) ∧
            (∀ a ∈ E, Algebra.trace (ZMod 2) K (a * (p.val.1 + p.val.2)) = 0) := hg
        rw [if_pos hg, k4GeneralTrace_joint_filter E p.val.2
          (p.val.1 + p.val.2), if_pos hc]
        norm_num [hcard]
      · have hc : ¬ ((∀ a ∈ E, Algebra.trace (ZMod 2) K (a * p.val.2) = 0) ∧
            (∀ a ∈ E, Algebra.trace (ZMod 2) K (a * (p.val.1 + p.val.2)) = 0)) := hg
        rw [if_neg hg, k4GeneralTrace_joint_filter E p.val.2
          (p.val.1 + p.val.2), if_neg hc]
    _ = ∑ r : E, ∑ s : E, k4ASWFourierCoefficient (s : K) (r : K) :=
      k4GeneralTrace_normOne_fourier_expansion n hn hfinrank E

theorem k5GeneralTrace_fourier_sum_lower (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K = n)
    (E : Submodule (ZMod 2) K) (hcard : Fintype.card E = 8) :
    (Fintype.card K : ℝ) + 1 - 126 * Real.sqrt (Fintype.card K : ℝ) - 252 ≤
      ∑ r : E, ∑ s : E, k4ASWFourierCoefficient (s : K) (r : K) := by
  classical
  let α := E × E
  let f : α → ℝ := fun z => k4ASWFourierCoefficient (z.2 : K) (z.1 : K)
  let z : α := (⟨0, E.zero_mem⟩, ⟨0, E.zero_mem⟩)
  have hcardα : Fintype.card α = 64 := by simp [α, hcard]
  have hzmem : z ∈ (Finset.univ : Finset α) := by simp
  have hzerof : f z = (Fintype.card K : ℝ) + 1 := by
    simp [f, z, k4ASWFourierCoefficient, k4ASWFourierValue]
  have hrest :
      ∑ x ∈ (Finset.univ : Finset α).erase z, f x ≥
        (63 : ℝ) * (-2 * Real.sqrt (Fintype.card K : ℝ) - 4) := by
    have hpoint : ∀ x ∈ (Finset.univ : Finset α).erase z,
        -2 * Real.sqrt (Fintype.card K : ℝ) - 4 ≤ f x := by
      intro x hx
      have hxne : x ≠ z := (Finset.mem_erase.mp hx).1
      have hpair : (x.1 : K) ≠ 0 ∨ (x.2 : K) ≠ 0 := by
        by_contra h
        have hfirst : (x.1 : K) = 0 := by
          by_contra hfirst
          exact h (Or.inl hfirst)
        have hsecond : (x.2 : K) = 0 := by
          by_contra hsecond
          exact h (Or.inr hsecond)
        apply hxne
        apply Prod.ext
        · exact Subtype.ext hfirst
        · exact Subtype.ext hsecond
      exact k4ASWFourierCoefficient_lower_of_hasse n hn hfinrank
        (x.2 : K) (x.1 : K) (Or.symm hpair)
    have hsum := Finset.sum_le_sum hpoint
    have herase : ((Finset.univ : Finset α).erase z).card = 63 := by
      rw [Finset.card_erase_of_mem hzmem]
      simp [hcardα]
    calc
      (63 : ℝ) * (-2 * Real.sqrt (Fintype.card K : ℝ) - 4) =
          ∑ x ∈ (Finset.univ : Finset α).erase z,
            (-2 * Real.sqrt (Fintype.card K : ℝ) - 4) := by
        simp [herase]
        ring
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).erase z, f x := hsum
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset α) f hzmem
  have htotal : ∑ x : α, f x =
      f z + ∑ x ∈ (Finset.univ : Finset α).erase z, f x := by
    calc
      ∑ x : α, f x =
          (∑ x ∈ (Finset.univ : Finset α).erase z, f x) + f z := hsplit.symm
      _ = f z + ∑ x ∈ (Finset.univ : Finset α).erase z, f x := by ring
  have hbound := add_le_add_left hrest (f z)
  rw [hzerof] at hbound
  have hfinal :
      (Fintype.card K : ℝ) + 1 - 126 * Real.sqrt (Fintype.card K : ℝ) - 252 ≤
        ∑ x : α, f x := by
    rw [htotal]
    nlinarith
  simpa [α, f, Fintype.sum_prod_type] using hfinal

theorem k5GeneralTraceGood_card_gt_three (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K = n)
    (E : Submodule (ZMod 2) K) (hcard : Fintype.card E = 8)
    (hq : 65536 ≤ Fintype.card K) :
    3 < Fintype.card {p : k4NormOnePairs (K := K) // k4GeneralTraceGood E p} := by
  let N := Fintype.card {p : k4NormOnePairs (K := K) // k4GeneralTraceGood E p}
  have hsum := k5GeneralTraceGood_card_fourier_sum n hn hfinrank E hcard
  have hlow := k5GeneralTrace_fourier_sum_lower n hn hfinrank E hcard
  rw [← hsum] at hlow
  have hqR : (65536 : ℝ) ≤ Fintype.card K := by exact_mod_cast hq
  have hsq : (Real.sqrt (Fintype.card K : ℝ)) ^ 2 = Fintype.card K :=
    Real.sq_sqrt (by positivity)
  have hsqrt : (256 : ℝ) ≤ Real.sqrt (Fintype.card K : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hq
  by_contra hnot
  have hN : N ≤ 3 := by omega
  have hNr : (N : ℝ) ≤ 3 := by exact_mod_cast hN
  change (Fintype.card K : ℝ) + 1 -
    126 * Real.sqrt (Fintype.card K : ℝ) - 252 ≤ (N : ℝ) * 64 at hlow
  nlinarith

#print axioms k5GeneralTraceGood_card_fourier_sum
#print axioms k5GeneralTrace_fourier_sum_lower
#print axioms k5GeneralTraceGood_card_gt_three
end Carlet
