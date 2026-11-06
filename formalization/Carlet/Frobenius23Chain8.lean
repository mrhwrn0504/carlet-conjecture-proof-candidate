import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain7
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_19 : f23 ∣ frobPoly 19+r23_19 := by
  have h18 := f23_dvd_frob_plus_18
  have h19 : f23 ∣ frobPoly 19+r23_19 := by
    exact f23_frob_step 18 h18 f23_rel_18
  exact h19
#print axioms f23_dvd_frob_plus_19
