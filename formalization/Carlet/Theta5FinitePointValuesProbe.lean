import Carlet.Theta5Probe
import Mathlib.Tactic

noncomputable section
namespace Carlet

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem theta5_eval_unit (i : Fin 5) :
    MvPolynomial.eval (fun j : Fin 5 => if j = i then (1 : ZMod 2) else 0) theta5 = 1 := by
  fin_cases i <;> simp [theta5, theta5Part0, theta5Part1, theta5Part2,
    theta5Part3, theta5Part4, theta5Part5, theta5Part6, theta5Part7, theta5X]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
theorem theta5_eval_two_distinct_units (i j : Fin 5) (hij : i ≠ j) :
    MvPolynomial.eval (fun k : Fin 5 => if k = i ∨ k = j then (1 : ZMod 2) else 0)
      theta5 = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [theta5, theta5Part0, theta5Part1, theta5Part2,
      theta5Part3, theta5Part4, theta5Part5, theta5Part6, theta5Part7, theta5X] <;>
    norm_num <;> exact CharP.cast_eq_zero (ZMod 2) 2

#print axioms theta5_eval_unit
#print axioms theta5_eval_two_distinct_units
end Carlet
