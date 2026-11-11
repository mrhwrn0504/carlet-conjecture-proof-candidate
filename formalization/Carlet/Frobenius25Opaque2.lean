import Carlet.Frobenius25OpaqueBase
import Carlet.Frobenius25Rel1
import Carlet.Frobenius25Rel2
import Carlet.Frobenius25Rel3
import Carlet.Frobenius25Rel4
import Carlet.Frobenius25Rel5
import Carlet.Frobenius25Opaque1
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem f25_opaque_10 : f25 ∣ frobPoly 10 + r25_10 := by
  have h5 := f25_opaque_5
  have h6 : f25 ∣ frobPoly 6 + r25_6 := f25_frob_step 5 h5 f25_rel_5
  have h7 : f25 ∣ frobPoly 7 + r25_7 := f25_frob_step 6 h6 f25_rel_6
  have h8 : f25 ∣ frobPoly 8 + r25_8 := f25_frob_step 7 h7 f25_rel_7
  have h9 : f25 ∣ frobPoly 9 + r25_9 := f25_frob_step 8 h8 f25_rel_8
  have h10 : f25 ∣ frobPoly 10 + r25_10 := f25_frob_step 9 h9 f25_rel_9
  exact h10
#print axioms f25_opaque_10
