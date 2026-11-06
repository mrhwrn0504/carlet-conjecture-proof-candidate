import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius17Probe
import Carlet.Frobenius23Frob
import Carlet.Frobenius23DegreeCriterionProbe
open Polynomial
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
lemma f23_irreducible : Irreducible f23 := by
  have hm : f23.Monic := by unfold f23; monicity <;> norm_num
  have hd : f23.natDegree = 23 := by
    have hp : ((X:P17)^23).natDegree = 23 := Polynomial.natDegree_X_pow 23
    have hs : (X^5+1:P17).natDegree ≤ 5 := by
      calc _ ≤ max (X^5:P17).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
        _ = 5 := by simp
    have hlt : (X^5+1:P17).natDegree < ((X:P17)^23).natDegree := by rw [hp]; omega
    have he : f23 = (X:P17)^23 + (X^5+1) := by unfold f23; ring
    rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]; exact hp
  have h0 : f23 ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
  have hne : f23 ≠ 1 := by intro h; have hh := congrArg Polynomial.natDegree h; rw [hd] at hh; norm_num at hh
  rw [Polynomial.Monic.irreducible_iff_degree_lt hm hne]
  intro q hqdeg hqf
  by_contra hqnot
  obtain ⟨g, hgm, hgi, hgq⟩ := Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0 : q ≠ 0 := by intro h; subst q; simp at hqf; exact h0 hqf
  have hqN : q.natDegree ≤ 11 := by
    rw [Polynomial.degree_eq_natDegree hq0] at hqdeg; rw [hd] at hqdeg; norm_num at hqdeg; exact_mod_cast hqdeg
  have hgN : g.natDegree ≤ 11 := (Polynomial.natDegree_le_of_dvd hgq hq0).trans hqN
  have hgf9 : g ∣ f23 := dvd_trans hgq hqf
  have hgf : g ∣ frobPoly 23-X := dvd_trans hgf9 f23_dvd_frobPoly_sub
  have hdiv : g.natDegree ∣ 23 := (irreducible_degree_dvd_frobPoly g hgi 23).2 hgf
  have hdiv1 : g.natDegree ∣ 1 := by interval_cases hdeg : g.natDegree <;> norm_num [hdeg] at *
  have hg2 : g ∣ (X:P17)^2-X := by
    have hh := (irreducible_degree_dvd_frobPoly g hgi 1).1 hdiv1
    simpa [frobPoly_eq_pow] using hh
  have hneg : -(X:P17) = X := by
    have hx : (X:P17)+X=0 := by
      have ht := congrArg (fun z:P17 => z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  have hg2plus : g ∣ (X:P17)^2+X := by simpa [sub_eq_add_neg, hneg] using hg2
  have hone : g ∣ (1:P17) := by rw [← f23_bezout]; exact dvd_add (dvd_mul_of_dvd_right hgf9 _) (dvd_mul_of_dvd_right hg2plus _) 
  exact hgi.not_isUnit (isUnit_of_dvd_one hone)
#print axioms f23_dvd_frobPoly_sub
#print axioms f23_irreducible
