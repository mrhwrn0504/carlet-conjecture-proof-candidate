import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain3
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_15 : f23 ∣ frobPoly 15+r23_15 := by
  have h12 := f23_dvd_frob_plus_12
  have h13 : f23 ∣ frobPoly 13+r23_13 := by
    exact f23_frob_step 12 h12 f23_rel_12
  have h14 : f23 ∣ frobPoly 14+r23_14 := by
    exact f23_frob_step 13 h13 f23_rel_13
  have h15 : f23 ∣ frobPoly 15+r23_15 := by
    exact f23_frob_step 14 h14 f23_rel_14
  exact h15
#print axioms f23_dvd_frob_plus_15
