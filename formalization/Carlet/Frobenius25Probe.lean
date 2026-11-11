import Carlet.Frobenius25Opaque5
import Carlet.Frobenius23DegreeCriterionProbe
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
lemma f25_bezout : (1 + X^1 + X^5 + X^8 + X^9 + X^10 + X^11 + X^15 + X^16 + X^18 + X^19 + X^20 + X^21 + X^22 + X^26 + X^29 + X^30)*f25 + (1 + X^2 + X^3 + X^4 + X^8 + X^9 + X^11 + X^12 + X^13 + X^14 + X^15 + X^19 + X^22 + X^23)*((X:P17)^32+X) = 1 := by
  unfold f25; ring_nf <;> simp [c2_17, c3_17, c4_17, c5_17, c6_17, c7_17, c8_17, c9_17, c10_17, c11_17, c12_17, c13_17, c14_17, c15_17, c16_17, c17_17, c18_17, c19_17, c20_17, c21_17, c22_17, c23_17, c24_17]
theorem f25_dvd_frobPoly_sub : f25 ∣ frobPoly 25 - X := by
  have h := f25_opaque_25
  have hneg : -(X:P17) = X := by
    have hx : (X:P17) + X = 0 := by
      have ht := congrArg (fun z : P17 => z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  simpa [r25_25, sub_eq_add_neg, hneg] using h
lemma f25_irreducible : Irreducible f25 := by
  have hm : f25.Monic := by unfold f25; monicity <;> norm_num
  have hd : f25.natDegree = 25 := by
    have hp : ((X:P17)^25).natDegree = 25 := Polynomial.natDegree_X_pow 25
    have hs : (X^3+1:P17).natDegree ≤ 3 := by
      calc _ ≤ max (X^3:P17).natDegree (1:P17).natDegree := Polynomial.natDegree_add_le _ _
        _ = 3 := by simp
    have hlt : (X^3+1:P17).natDegree < ((X:P17)^25).natDegree := by rw [hp]; omega
    have he : f25 = (X:P17)^25 + (X^3+1) := by unfold f25; ring
    rw [he, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]; exact hp
  have h0 : f25 ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
  have hne : f25 ≠ 1 := by intro h; have hh := congrArg Polynomial.natDegree h; rw [hd] at hh; norm_num at hh
  rw [Polynomial.Monic.irreducible_iff_degree_lt hm hne]
  intro q hqdeg hqf
  by_contra hqnot
  obtain ⟨g, hgm, hgi, hgq⟩ := Polynomial.exists_monic_irreducible_factor q hqnot
  have hq0 : q ≠ 0 := by intro h; subst q; simp at hqf; exact h0 hqf
  have hqN : q.natDegree ≤ 12 := by
    rw [Polynomial.degree_eq_natDegree hq0] at hqdeg; rw [hd] at hqdeg; norm_num at hqdeg; exact_mod_cast hqdeg
  have hgN : g.natDegree ≤ 12 := (Polynomial.natDegree_le_of_dvd hgq hq0).trans hqN
  have hgf9 : g ∣ f25 := dvd_trans hgq hqf
  have hgf : g ∣ frobPoly 25-X := dvd_trans hgf9 f25_dvd_frobPoly_sub
  have hdiv : g.natDegree ∣ 25 := (irreducible_degree_dvd_frobPoly g hgi 25).2 hgf
  have hdiv1 : g.natDegree ∣ 5 := by interval_cases hdeg : g.natDegree <;> norm_num [hdeg] at *
  have hg2 : g ∣ (X:P17)^32-X := by
    have hh := (irreducible_degree_dvd_frobPoly g hgi 5).1 hdiv1
    simpa [frobPoly_eq_pow] using hh
  have hneg : -(X:P17) = X := by
    have hx : (X:P17)+X=0 := by
      have ht := congrArg (fun z:P17 => z*X) c2_17
      simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  have hg2plus : g ∣ (X:P17)^32+X := by simpa [sub_eq_add_neg, hneg] using hg2
  have hone : g ∣ (1:P17) := by rw [← f25_bezout]; exact dvd_add (dvd_mul_of_dvd_right hgf9 _) (dvd_mul_of_dvd_right hg2plus _) 
  exact hgi.not_isUnit (isUnit_of_dvd_one hone)
#print axioms f25_irreducible
