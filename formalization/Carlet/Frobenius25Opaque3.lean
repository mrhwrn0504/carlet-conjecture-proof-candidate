import Carlet.Frobenius25OpaqueBase
import Carlet.Frobenius25Rel1
import Carlet.Frobenius25Rel2
import Carlet.Frobenius25Rel3
import Carlet.Frobenius25Rel4
import Carlet.Frobenius25Rel5
import Carlet.Frobenius25Opaque2
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem f25_opaque_15 : f25 ∣ frobPoly 15 + r25_15 := by
  have h10 := f25_opaque_10
  have h11 : f25 ∣ frobPoly 11 + r25_11 := f25_frob_step 10 h10 f25_rel_10
  have h12 : f25 ∣ frobPoly 12 + r25_12 := f25_frob_step 11 h11 f25_rel_11
  have h13 : f25 ∣ frobPoly 13 + r25_13 := f25_frob_step 12 h12 f25_rel_12
  have h14 : f25 ∣ frobPoly 14 + r25_14 := f25_frob_step 13 h13 f25_rel_13
  have h15 : f25 ∣ frobPoly 15 + r25_15 := f25_frob_step 14 h14 f25_rel_14
  exact h15
#print axioms f25_opaque_15
