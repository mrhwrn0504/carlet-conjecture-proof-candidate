import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain1
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_8 : f23 ∣ frobPoly 8+r23_8 := by
  have h4 := f23_dvd_frob_plus_4
  have h5 : f23 ∣ frobPoly 5+r23_5 := by
    exact f23_frob_step 4 h4 f23_rel_4
  have h6 : f23 ∣ frobPoly 6+r23_6 := by
    exact f23_frob_step 5 h5 f23_rel_5
  have h7 : f23 ∣ frobPoly 7+r23_7 := by
    exact f23_frob_step 6 h6 f23_rel_6
  have h8 : f23 ∣ frobPoly 8+r23_8 := by
    exact f23_frob_step 7 h7 f23_rel_7
  exact h8
#print axioms f23_dvd_frob_plus_8
