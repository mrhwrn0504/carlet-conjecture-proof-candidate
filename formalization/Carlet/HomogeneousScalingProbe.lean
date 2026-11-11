import Mathlib.RingTheory.MvPolynomial.Homogeneous

universe u v w

private theorem weightOne_eq_degree {σ : Type u} :
    Finsupp.weight (fun _ : σ => 1) = Finsupp.degree := by
  apply AddMonoidHom.ext
  intro d
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i a d hi ha ih =>
      rw [map_add, map_add, ih]
      simp [Finsupp.weight_single]

lemma aeval_smul_of_isHomogeneous {R : Type v} {S : Type w} {σ : Type u}
    [CommSemiring R] [CommSemiring S] [Algebra R S] (c : S) (g : σ → S)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (fun i => c * g i) p = c ^ d * MvPolynomial.aeval g p := by
  classical
  have hsum : p = ∑ e ∈ p.support, (MvPolynomial.monomial e) (MvPolynomial.coeff e p) :=
    MvPolynomial.as_sum p
  have hmap : (MvPolynomial.aeval g) p =
      ∑ e ∈ p.support, (MvPolynomial.aeval g)
        ((MvPolynomial.monomial e) (MvPolynomial.coeff e p)) := by
    calc
      (MvPolynomial.aeval g) p =
          (MvPolynomial.aeval g)
            (∑ e ∈ p.support, (MvPolynomial.monomial e) (MvPolynomial.coeff e p)) := by
              conv_lhs => rw [hsum]
      _ = _ := by rw [map_sum]
  conv_lhs => rw [hsum]
  rw [map_sum]
  calc
    (∑ e ∈ p.support,
        (MvPolynomial.aeval fun i => c * g i) ((MvPolynomial.monomial e) (MvPolynomial.coeff e p))) =
      c ^ d * ∑ e ∈ p.support,
        (MvPolynomial.aeval g) ((MvPolynomial.monomial e) (MvPolynomial.coeff e p)) := by
          conv_rhs => rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          have heSupport : MvPolynomial.coeff e p ≠ 0 := by
            intro hz
            exact (MvPolynomial.mem_support_iff.mp he) hz
          have heDegreeW := hp heSupport
          have heDegree : Finsupp.degree e = d := by
            have hweight : (Finsupp.weight (fun _ : σ => 1)) e = Finsupp.degree e :=
              congrArg (fun f => f e) weightOne_eq_degree
            change (Finsupp.weight (fun _ : σ => 1)) e = d at heDegreeW
            rw [hweight] at heDegreeW
            exact heDegreeW
          rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
          have hprod : e.prod (fun i k => (c * g i) ^ k) =
              c ^ Finsupp.degree e * e.prod (fun i k => g i ^ k) := by
            calc
              e.prod (fun i k => (c * g i) ^ k) =
                  e.prod (fun i k => c ^ k * g i ^ k) := by
                    apply Finsupp.prod_congr
                    intro i hi
                    simp [mul_pow]
              _ = e.prod (fun i k => c ^ k) * e.prod (fun i k => g i ^ k) := by
                    rw [Finsupp.prod_mul]
              _ = c ^ Finsupp.degree e * e.prod (fun i k => g i ^ k) := by
                    congr 1
                    change (∏ i ∈ e.support, c ^ e i) = c ^ Finsupp.degree e
                    rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
          rw [hprod, heDegree]
          ring
    _ = c ^ d * (MvPolynomial.aeval g) p := by
          exact congrArg (fun z => c ^ d * z) hmap.symm


