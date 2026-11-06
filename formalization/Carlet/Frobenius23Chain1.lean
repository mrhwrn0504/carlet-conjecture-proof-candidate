import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_4 : f23 ∣ frobPoly 4+r23_4 := by
  have h0 : f23 ∣ frobPoly 0+r23_0 := by
    have hx:(X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
    have he:frobPoly 0+r23_0=0 := by simpa [r23_0, frobPoly_zero] using hx
    rw [he]; exact dvd_zero f23
  have h1 : f23 ∣ frobPoly 1+r23_1 := by
    exact f23_frob_step 0 h0 f23_rel_0
  have h2 : f23 ∣ frobPoly 2+r23_2 := by
    exact f23_frob_step 1 h1 f23_rel_1
  have h3 : f23 ∣ frobPoly 3+r23_3 := by
    exact f23_frob_step 2 h2 f23_rel_2
  have h4 : f23 ∣ frobPoly 4+r23_4 := by
    exact f23_frob_step 3 h3 f23_rel_3
  exact h4
#print axioms f23_dvd_frob_plus_4
