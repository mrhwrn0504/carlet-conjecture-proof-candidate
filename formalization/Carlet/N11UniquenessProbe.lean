import Carlet.Frobenius11Scratch
import Carlet.N11AllInverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
lemma f_natDegree_unique_probe : f.natDegree = 11 := by
  unfold f
  rw [add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 11
  · have hsmall : ((X : P)^2 + 1).natDegree = 2 := by
      simpa using (Polynomial.natDegree_X_pow_add_C (n := 2) (r := (1 : F)))
    rw [Polynomial.natDegree_X_pow, hsmall]
    norm_num
theorem adjoin_mk_injective_below_11 {p q : P}
    (hp : p.natDegree < 11) (hq : q.natDegree < 11)
    (h : AdjoinRoot.mk f p = AdjoinRoot.mk f q) : p = q := by
  by_contra hpq
  have hdvd : f ∣ p - q := AdjoinRoot.mk_eq_mk.mp h
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  have hlt : (p-q).natDegree < f.natDegree := by
    rw [f_natDegree_unique_probe]
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le p q) (max_lt_iff.mpr ⟨hp,hq⟩)
  omega
theorem certV01_ne_certV02 : certV01 ≠ certV02 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 10) h
  simp only [certV01, certV02, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc; norm_num at hc
#print axioms adjoin_mk_injective_below_11






lemma certV01_degree_lt : certV01.natDegree < 11 := by
  unfold certV01
  compute_degree!

lemma certV02_degree_lt : certV02.natDegree < 11 := by
  unfold certV02
  compute_degree!

example : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV02 := by
  intro h
  have hp := adjoin_mk_injective_below_11 certV01_degree_lt certV02_degree_lt h
  exact certV01_ne_certV02 hp




