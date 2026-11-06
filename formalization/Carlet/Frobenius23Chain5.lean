import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain4
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_16 : f23 ∣ frobPoly 16+r23_16 := by
  have h15 := f23_dvd_frob_plus_15
  have h16 : f23 ∣ frobPoly 16+r23_16 := by
    exact f23_frob_step 15 h15 f23_rel_15
  exact h16
#print axioms f23_dvd_frob_plus_16
