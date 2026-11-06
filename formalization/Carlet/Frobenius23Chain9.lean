import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain8
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_20 : f23 ∣ frobPoly 20+r23_20 := by
  have h19 := f23_dvd_frob_plus_19
  have h20 : f23 ∣ frobPoly 20+r23_20 := by
    exact f23_frob_step 19 h19 f23_rel_19
  exact h20
#print axioms f23_dvd_frob_plus_20
