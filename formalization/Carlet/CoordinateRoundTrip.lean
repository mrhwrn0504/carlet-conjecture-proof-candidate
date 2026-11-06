import Carlet.ForwardCoordinates

noncomputable section

open Polynomial
open scoped Ring

namespace Carlet.Quadratic

variable {A : Type*} [CommRing A]

theorem rows_kernel_eq_reconstructed (h2 : (2 : A) = 0)
    (c : ℕ → A) (u : ℕ → ℕ → A) (r n : ℕ) (hn : n ≤ r)
    (h : TriangularRelations c u r) :
    kernelPolynomial (fun j => u j 0) n = reconstructedPolynomial c n := by
  rw [← indexedProduct_eq_kernel h2, rows_indexedProduct h2 c u r h n hn]

theorem rows_delta_eq_scale (h2 : (2 : A) = 0)
    (c : ℕ → A) (u : ℕ → ℕ → A) (r n : ℕ) (hn : n < r)
    (h : TriangularRelations c u r) : delta (fun j => u j 0) n = scale c n := by
  rw [delta, rows_kernel_eq_reconstructed h2 c u r n (Nat.le_of_lt hn) h,
    row_eval_scale c u r h n hn]

theorem reverse_then_forward_c (h2 : (2 : A) = 0)
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r n : ℕ) (hn : n+1 < r)
    (h : QuadraticCondition c t d u r) : forwardC (fun j => u j 0) n = c n := by
  obtain ⟨hu, ht0, ht, hc, hsum⟩ := h
  have hn0 : n < r := by omega
  rw [forwardC, rows_delta_eq_scale h2 c u r (n+1) hn hu,
    rows_delta_eq_scale h2 c u r n hn0 hu, scale, mul_assoc,
    Ring.mul_inverse_cancel _ ((bounded_scale_isUnit c t d r n hn0 ht hc).pow 2), mul_one]

theorem reverse_then_forward_t [Algebra (ZMod 2) A]
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ) (hr : 0 < r)
    (h : QuadraticCondition c t d u r) (n : ℕ) (hn : n < r) :
    forwardT (fun j => u j 0) n = t n := by
  obtain ⟨hu, ht0, ht, hc, hsum⟩ := h
  have hx := reverse_satisfies_openCarlet c t d u r hr hu ht0 ht hc hsum
  rw [forwardT_eq_blockSum algebra_two_eq_zero (fun j => u j 0) r n hn hx.1 hx.2.1,
    rows_blockSum_eq_t algebra_two_eq_zero c t d u r hu ht0 ht hc n hn]

theorem reverse_then_forward_d [Algebra (ZMod 2) A]
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ) (hr : 0 < r)
    (h : QuadraticCondition c t d u r) (n : ℕ) (hn : n < r) :
    forwardD (fun j => u j 0) n = d n := by
  rw [forwardD, reverse_then_forward_t c t d u r hr h n hn]
  have ht := h.2.2.1 n hn
  apply (coordinate_isUnit _ _ ht).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (coordinate_isUnit _ _ ht), ht]

theorem reverse_then_forward_u [Algebra (ZMod 2) A]
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r a j : ℕ)
    (h : QuadraticCondition c t d u r) (ha : a < r) (hj : j ≤ a) :
    forwardU (fun k => u k 0) a j = u a j := by
  obtain ⟨hu, ht0, ht, hc, hsum⟩ := h
  have hjr : j < r := lt_of_le_of_lt hj ha
  rw [forwardU, rows_kernel_eq_reconstructed algebra_two_eq_zero c u r j (by omega) hu,
    rows_delta_eq_scale algebra_two_eq_zero c u r j hjr hu]
  exact rows_recover_all_coordinates c u r hu a j ha hj _
    (Ring.mul_inverse_cancel _ (bounded_scale_isUnit c t d r j hjr ht hc))

theorem reverse_then_forward_all [Algebra (ZMod 2) A]
    (c t d : ℕ → A) (u : ℕ → ℕ → A) (r : ℕ) (hr : 0 < r)
    (h : QuadraticCondition c t d u r) :
    (∀ j, j+1 < r → forwardC (fun k => u k 0) j = c j) ∧
    (∀ j < r, forwardT (fun k => u k 0) j = t j) ∧
    (∀ j < r, forwardD (fun k => u k 0) j = d j) ∧
    (∀ a < r, ∀ j ≤ a, forwardU (fun k => u k 0) a j = u a j) := by
  exact ⟨fun j hj => reverse_then_forward_c algebra_two_eq_zero c t d u r j hj h,
    fun j hj => reverse_then_forward_t c t d u r hr h j hj,
    fun j hj => reverse_then_forward_d c t d u r hr h j hj,
    fun a ha j hj => reverse_then_forward_u c t d u r a j h ha hj⟩

#print axioms reverse_then_forward_all

end Carlet.Quadratic
