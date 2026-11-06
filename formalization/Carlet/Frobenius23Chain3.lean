import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Chain2
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_12 : f23 ∣ frobPoly 12+r23_12 := by
  have h8 := f23_dvd_frob_plus_8
  have h9 : f23 ∣ frobPoly 9+r23_9 := by
    exact f23_frob_step 8 h8 f23_rel_8
  have h10 : f23 ∣ frobPoly 10+r23_10 := by
    exact f23_frob_step 9 h9 f23_rel_9
  have h11 : f23 ∣ frobPoly 11+r23_11 := by
    exact f23_frob_step 10 h10 f23_rel_10
  have h12 : f23 ∣ frobPoly 12+r23_12 := by
    exact f23_frob_step 11 h11 f23_rel_11
  exact h12
#print axioms f23_dvd_frob_plus_12
