import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain5
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_17 : f23 ∣ frobPoly 17+r23_17 := by
  have h16 := f23_dvd_frob_plus_16
  have h17 : f23 ∣ frobPoly 17+r23_17 := by
    exact f23_frob_step 16 h16 f23_rel_16
  exact h17
#print axioms f23_dvd_frob_plus_17
