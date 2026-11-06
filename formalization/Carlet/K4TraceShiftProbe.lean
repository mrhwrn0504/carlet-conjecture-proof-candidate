import Carlet.ArtinSchreier

noncomputable section
namespace Carlet

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

omit [Fintype K] in
/-- The last trace test is unchanged by the two choices of an AS root. -/
theorem k4_trace_mul_shift_one (u s : K)
    (hu : Algebra.trace (ZMod 2) K u = 0) :
    Algebra.trace (ZMod 2) K (u*(s+1)) = Algebra.trace (ZMod 2) K (u*s) := by
  have h : u*(s+1) = u*s+u := by ring
  rw [h, map_add, hu, add_zero]

/-- Replacing the preceding AS root by its other choice shifts s by u. -/
theorem k4_trace_mul_shift_u (u s : K)
    (hu : Algebra.trace (ZMod 2) K u = 0) :
    Algebra.trace (ZMod 2) K (u*(s+u)) = Algebra.trace (ZMod 2) K (u*s) := by
  have h : u*(s+u) = u*s+u^2 := by ring
  rw [h, map_add, trace_square, hu, add_zero]

theorem k4_trace_u_mul_succ (u : K) :
    Algebra.trace (ZMod 2) K (u*(u+1)) = 0 := by
  have h : u*(u+1) = u^2+u := by ring
  rw [h, map_add, trace_square, CharTwo.add_self_eq_zero]

/-- Move an Artin–Schreier operator from one factor to the other inside the trace. -/
theorem k4_trace_as_pair (b z : K) :
    Algebra.trace (ZMod 2) K ((b^2+b)*z) =
      Algebra.trace (ZMod 2) K (b^2*(z^2+z)) := by
  have h1 : (b^2+b)*z = b^2*z+b*z := by ring
  have h2 : b^2*(z^2+z) = (b*z)^2+b^2*z := by ring
  rw [h1, h2, map_add, map_add, trace_square, add_comm]

theorem k4_trace_second_shift (t : K) :
    Algebra.trace (ZMod 2) K (t^2*(t^2+t)*((t^2+t)+1)) = 0 := by
  let u := t^2+t
  have hu : Algebra.trace (ZMod 2) K u = 0 := by
    dsimp [u]
    rw [map_add, trace_square, CharTwo.add_self_eq_zero]
  have hpoly : t^2*u*(u+1) = (t*u)^2+t^2*u := by ring
  change Algebra.trace (ZMod 2) K (t^2*u*(u+1)) = 0
  rw [hpoly, map_add, trace_square]
  have hsum : t*u+t^2*u = u^2 := by dsimp [u]; ring
  rw [← map_add, hsum, trace_square, hu]

theorem k4_trace_first_test_shift (u z : K) :
    Algebra.trace (ZMod 2) K (u*(u+1)*(z+1)) =
      Algebra.trace (ZMod 2) K (u*(u+1)*z) := by
  have h : u*(u+1)*(z+1) = u*(u+1)*z + u*(u+1) := by ring
  rw [h, map_add, k4_trace_u_mul_succ, add_zero]

theorem k4_trace_second_test_shift (t z : K) :
    Algebra.trace (ZMod 2) K (t^2*(t^2+t)*((t^2+t)+1)*(z+1)) =
      Algebra.trace (ZMod 2) K (t^2*(t^2+t)*((t^2+t)+1)*z) := by
  have h : t^2*(t^2+t)*((t^2+t)+1)*(z+1) =
      t^2*(t^2+t)*((t^2+t)+1)*z + t^2*(t^2+t)*((t^2+t)+1) := by ring
  rw [h, map_add, k4_trace_second_shift, add_zero]

#print axioms k4_trace_mul_shift_one
#print axioms k4_trace_mul_shift_u
#print axioms k4_trace_first_test_shift
#print axioms k4_trace_second_test_shift
#print axioms k4_trace_as_pair
end Carlet
