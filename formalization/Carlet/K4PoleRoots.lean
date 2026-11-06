import Carlet.K4PoleNumerator

noncomputable section
open Polynomial

namespace Carlet

variable {L : Type*} [Field L] [IsAlgClosed L] [Algebra (ZMod 2) L]

local instance : CharP L 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2

noncomputable local instance : DecidableEq L := Classical.decEq _

omit [IsAlgClosed L] [Algebra (ZMod 2) L] in
theorem k4_pole_den_degree : (k4PoleDenPoly L).natDegree = 6 := by
  unfold k4PoleDenPoly
  compute_degree!

omit [IsAlgClosed L] in
theorem k4_pole_den_separable : (k4PoleDenPoly L).Separable := by
  simpa only [separable_def] using k4_pole_den_coprime_derivative (K := L)

omit [Algebra (ZMod 2) L] in
theorem k4_pole_den_roots_card : (k4PoleDenPoly L).roots.card = 6 := by
  have hsplit : (k4PoleDenPoly L).Splits := IsAlgClosed.splits _
  rw [← hsplit.natDegree_eq_card_roots, k4_pole_den_degree]

omit [IsAlgClosed L] in
theorem k4_pole_den_roots_nodup : (k4PoleDenPoly L).roots.Nodup :=
  nodup_roots k4_pole_den_separable

theorem k4_pole_den_roots_toFinset_card :
    (k4PoleDenPoly L).roots.toFinset.card = 6 := by
  rw [Multiset.toFinset_card_of_nodup k4_pole_den_roots_nodup,
    k4_pole_den_roots_card]

omit [IsAlgClosed L] in
theorem k4_pole_root_not_num_one (t : L)
    (hD : Polynomial.eval t (k4PoleDenPoly L) = 0) :
    Polynomial.eval t (k4PoleNumOnePoly L) ≠ 0 := by
  intro hN
  have h := congrArg (Polynomial.eval t) (k4_pole_num_one_bezout (K := L))
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at h
  rw [hD, hN] at h
  norm_num at h

omit [IsAlgClosed L] in
theorem k4_pole_root_not_num02 (t : L)
    (hD : Polynomial.eval t (k4PoleDenPoly L) = 0) :
    Polynomial.eval t (k4PoleNum02Poly L) ≠ 0 := by
  intro hN
  have h := congrArg (Polynomial.eval t) (k4_pole_num02_bezout (K := L))
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at h
  rw [hD, hN] at h
  norm_num at h

#print axioms k4_pole_den_degree
#print axioms k4_pole_den_separable
#print axioms k4_pole_den_roots_card
#print axioms k4_pole_den_roots_nodup
#print axioms k4_pole_den_roots_toFinset_card
#print axioms k4_pole_root_not_num_one
#print axioms k4_pole_root_not_num02

end Carlet
