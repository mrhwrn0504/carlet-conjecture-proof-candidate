import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain6
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_18 : f23 ∣ frobPoly 18+r23_18 := by
  have h17 := f23_dvd_frob_plus_17
  have h18 : f23 ∣ frobPoly 18+r23_18 := by
    exact f23_frob_step 17 h17 f23_rel_17
  exact h18
#print axioms f23_dvd_frob_plus_18
