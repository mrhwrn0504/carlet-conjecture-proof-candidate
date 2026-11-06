import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain9
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_21 : f23 ∣ frobPoly 21+r23_21 := by
  have h20 := f23_dvd_frob_plus_20
  have h21 : f23 ∣ frobPoly 21+r23_21 := by
    exact f23_frob_step 20 h20 f23_rel_20
  exact h21
#print axioms f23_dvd_frob_plus_21
