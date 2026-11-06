import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain10
open Polynomial
noncomputable section
set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_22 : f23 ∣ frobPoly 22+r23_22 := by
  have h21 := f23_dvd_frob_plus_21
  have h22 : f23 ∣ frobPoly 22+r23_22 := by
    exact f23_frob_step 21 h21 f23_rel_21
  exact h22
#print axioms f23_dvd_frob_plus_22
