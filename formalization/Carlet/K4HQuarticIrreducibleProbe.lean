import Carlet.K4HNoQuadraticFactorProbe
import Carlet.K4HNoLinearFactorProbe
import Carlet.K4MonicLowDegreeFormsProbe
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
open Polynomial
namespace Carlet
variable (K : Type*) [Field K] [Algebra (ZMod 2) K]

omit [Algebra (ZMod 2) K] in
theorem k4HQuartic_monic : (k4HQuartic K).Monic := by
  unfold k4HQuartic
  monicity <;> norm_num

omit [Algebra (ZMod 2) K] in
theorem k4HQuartic_natDegree : (k4HQuartic K).natDegree = 4 := by
  unfold k4HQuartic
  compute_degree <;> norm_num

theorem k4HQuartic_irreducible : Irreducible (k4HQuartic K) := by
  have hp1 : k4HQuartic K ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    rw [k4HQuartic_natDegree] at hd
    simp at hd
  rw [Polynomial.irreducible_of_monic (k4HQuartic_monic K) hp1]
  intro f g hf hg hfg
  by_cases hf0 : f.natDegree = 0
  · exact Or.inl (hf.natDegree_eq_zero.mp hf0)
  by_cases hg0 : g.natDegree = 0
  · exact Or.inr (hg.natDegree_eq_zero.mp hg0)
  have hsum : f.natDegree + g.natDegree = 4 := by
    rw [← hf.natDegree_mul hg, hfg, k4HQuartic_natDegree]
  have hcases : f.natDegree = 1 ∨ g.natDegree = 1 ∨
      (f.natDegree = 2 ∧ g.natDegree = 2) := by omega
  rcases hcases with hf1 | hg1 | ⟨hf2, hg2⟩
  · have hfzero : f.eval (-f.coeff 0) = 0 := by
      rw [monic_degree_one_form f hf hf1]
      simp
    have hpzero : (k4HQuartic K).eval (-f.coeff 0) = 0 := by
      rw [← hfg, Polynomial.eval_mul, hfzero, zero_mul]
    exact (k4HQuartic_no_polynomial_root K _ hpzero).elim
  · have hgzero : g.eval (-g.coeff 0) = 0 := by
      rw [monic_degree_one_form g hg hg1]
      simp
    have hpzero : (k4HQuartic K).eval (-g.coeff 0) = 0 := by
      rw [← hfg, Polynomial.eval_mul, hgzero, mul_zero]
    exact (k4HQuartic_no_polynomial_root K _ hpzero).elim
  · have hfForm := monic_degree_two_form f hf hf2
    have hgForm := monic_degree_two_form g hg hg2
    have hbad : k4HQuartic K =
        (X^2+C (f.coeff 1)*X+C (f.coeff 0)) *
        (X^2+C (g.coeff 1)*X+C (g.coeff 0)) := by
      rw [← hfForm, ← hgForm, hfg]
    exact (k4HQuartic_no_monic_quadratic_product K _ _ _ _ hbad).elim

#print axioms k4HQuartic_monic
#print axioms k4HQuartic_natDegree
#print axioms k4HQuartic_irreducible
end Carlet
