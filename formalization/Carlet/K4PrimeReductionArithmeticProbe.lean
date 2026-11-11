import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
namespace Carlet

theorem odd_degree_has_relevant_divisor (n : ℕ) (hn : Odd n) (hmin : 7 ≤ n)
    (h9 : ¬ 9 ∣ n) (h15 : ¬ 15 ∣ n) (h25 : ¬ 25 ∣ n) :
    ∃ p, Nat.Prime p ∧ 7 ≤ p ∧ p ∣ n := by
  have hodd2 : ¬ 2 ∣ n := by
    intro h
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := hn
    omega
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hp2 : p ≠ 2 := by intro h; subst p; exact hodd2 hpn
  by_cases hp3 : p = 3
  · subst p
    obtain ⟨m, hm⟩ := hpn
    have hm1 : m ≠ 1 := by omega
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hqn : q ∣ n := dvd_trans hqm ⟨3, by omega⟩
    have hq2 : q ≠ 2 := by intro h; subst q; exact hodd2 hqn
    have hq3 : q ≠ 3 := by
      intro h; subst q
      apply h9
      obtain ⟨v, hv⟩ := hqm
      refine ⟨v, ?_⟩
      omega
    have hq5 : q ≠ 5 := by
      intro h; subst q
      apply h15
      obtain ⟨v, hv⟩ := hqm
      refine ⟨v, ?_⟩
      omega
    refine ⟨q, hq, ?_, hqn⟩
    have hqmin := hq.two_le
    by_contra h; have : q ≤ 6 := by omega
    interval_cases q <;> norm_num at *
  by_cases hp5 : p = 5
  · subst p
    obtain ⟨m, hm⟩ := hpn
    have hm1 : m ≠ 1 := by omega
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hqn : q ∣ n := dvd_trans hqm ⟨5, by omega⟩
    have hq2 : q ≠ 2 := by intro h; subst q; exact hodd2 hqn
    have hq3 : q ≠ 3 := by
      intro h; subst q
      apply h15
      obtain ⟨v, hv⟩ := hqm
      refine ⟨v, ?_⟩
      omega
    have hq5 : q ≠ 5 := by
      intro h; subst q
      apply h25
      obtain ⟨v, hv⟩ := hqm
      refine ⟨v, ?_⟩
      omega
    refine ⟨q, hq, ?_, hqn⟩
    have hqmin := hq.two_le
    by_contra h; have : q ≤ 6 := by omega
    interval_cases q <;> norm_num at *
  refine ⟨p, hp, ?_, hpn⟩
  have hpmin := hp.two_le
  by_contra h; have : p ≤ 6 := by omega
  interval_cases p <;> norm_num at *

#print axioms odd_degree_has_relevant_divisor
end Carlet
