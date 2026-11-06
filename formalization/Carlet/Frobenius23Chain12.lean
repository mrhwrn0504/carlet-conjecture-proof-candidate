import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain11
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_23 : f23 ∣ frobPoly 23+r23_23 := by
  have h22 := f23_dvd_frob_plus_22
  have h23 : f23 ∣ frobPoly 23+r23_23 := by
    exact f23_frob_step 22 h22 f23_rel_22
  exact h23
#print axioms f23_dvd_frob_plus_23
