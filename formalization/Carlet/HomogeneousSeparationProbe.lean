import Mathlib.RingTheory.MvPolynomial.Homogeneous
lemma weight_one_eq_degree {σ : Type*} : Finsupp.weight (fun _ : σ => 1) = Finsupp.degree := by
  apply AddMonoidHom.ext
  intro d
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i a d hi ha ih =>
      rw [map_add, map_add, ih]
      simp [Finsupp.weight_single]
