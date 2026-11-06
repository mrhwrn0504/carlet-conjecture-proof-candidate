import Carlet.K4CoordCoverageProbe
import Carlet.K4ThetaSpanBridgeProbe

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Carlet

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

theorem theta4_relation_condition_implies_span_chain (x : Fin 4 → K)
    (hrel : ∀ r : Fin 4 → ZMod 2, r ≠ 0 →
      (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) ≠ 0) :
    x 0 ≠ 0 ∧ x 1 ∉ k4Span1 x ∧ x 2 ∉ k4Span2 x ∧ x 3 ∉ k4Span3 x := by
  have hchar : (1 : K) + 1 = 0 := one_add_one_eq_zero_over_field
  have haddself : ∀ z : K, z + z = 0 := by
    intro z
    have h := congrArg (fun w : K => w * z) hchar
    simpa [add_mul] using h
  have hcancel2 : ∀ u v : K, (u + v) + (u + v) = 0 := by
    intro u v
    calc
      (u + v) + (u + v) = (u + u) + (v + v) := by abel
      _ = 0 := by rw [haddself, haddself]; simp
  have hcancel3 : ∀ u v w : K, (u + v + w) + (u + v + w) = 0 := by
    intro u v w
    calc
      (u + v + w) + (u + v + w) = (u + u) + (v + v) + (w + w) := by abel
      _ = 0 := by simp [haddself]
  have h0 : x 0 ≠ 0 := by
    intro hx
    let r : Fin 4 → ZMod 2 := fun i => if i = 0 then 1 else 0
    have hr : r ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [r] at this
    have he : (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 := by
      simp [r, hx]
    exact (hrel r hr) he
  have h1 : x 1 ∉ k4Span1 x := by
    intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨a, ha⟩
    let r : Fin 4 → ZMod 2 := fun i => if i = 0 then a else if i = 1 then 1 else 0
    have hr : r ≠ 0 := by
      intro h
      have := congrFun h 1
      simp [r] at this
    have he : (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 := by
      calc
        _ = a • x 0 + x 1 := by simp [r, ← Algebra.smul_def, Fin.sum_univ_succ]
        _ = 0 := by rw [← ha]; exact haddself _
    exact (hrel r hr) he
  have h2 : x 2 ∉ k4Span2 x := by
    intro hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
    rcases Submodule.mem_span_singleton.mp hy with ⟨b, hb⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨a, ha⟩
    let r : Fin 4 → ZMod 2 := fun i =>
      if i = 0 then b else if i = 1 then a else if i = 2 then 1 else 0
    have hr : r ≠ 0 := by
      intro h
      have := congrFun h 2
      simp [r] at this
    have he : (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 := by
      calc
        _ = b • x 0 + (a • x 1 + x 2) := by
          simp [r, ← Algebra.smul_def, Fin.sum_univ_succ]
        _ = 0 := by
          rw [← hyz, ← hb, ← ha]
          simpa [add_assoc] using hcancel2 (b • x 0) (a • x 1)
    exact (hrel r hr) he
  have h3 : x 3 ∉ k4Span3 x := by
    intro hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
    rcases Submodule.mem_sup.mp hy with ⟨y0, hy0, y1, hy1, hy01⟩
    rcases Submodule.mem_span_singleton.mp hy0 with ⟨b, hb⟩
    rcases Submodule.mem_span_singleton.mp hy1 with ⟨a, ha⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, hc⟩
    let r : Fin 4 → ZMod 2 := fun i =>
      if i = 0 then b else if i = 1 then a else if i = 2 then c else 1
    have hr : r ≠ 0 := by
      intro h
      have := congrFun h 3
      simp [r] at this
    have he : (∑ i : Fin 4, algebraMap (ZMod 2) K (r i) * x i) = 0 := by
      calc
        _ = b • x 0 + (a • x 1 + (c • x 2 + x 3)) := by
          simp [r, ← Algebra.smul_def, Fin.sum_univ_succ]
        _ = 0 := by
          rw [← hyz, ← hy01, ← hb, ← ha, ← hc]
          simpa [add_assoc] using hcancel3 (b • x 0) (a • x 1) (c • x 2)
    exact (hrel r hr) he
  exact ⟨h0, h1, h2, h3⟩

variable [Fintype K] [DecidableEq K]

theorem hasZeroSumSubspace_four_of_theta4_large_zero_count
    (hcount : Fintype.card {x : Fin 4 → K //
      MvPolynomial.eval x (theta4.map (algebraMap (ZMod 2) K)) = 0} >
      120 * Fintype.card K ^ 2) : HasZeroSumSubspace K 4 := by
  obtain ⟨x, htheta, hrel⟩ := theta4_independent_zero_exists_of_large_zero_count hcount
  obtain ⟨h0, h1, h2, h3⟩ := theta4_relation_condition_implies_span_chain x hrel
  exact hasZeroSumSubspace_four_of_theta4_chain x h0 h1 h2 h3 htheta

#print axioms theta4_relation_condition_implies_span_chain
#print axioms hasZeroSumSubspace_four_of_theta4_large_zero_count
end Carlet
