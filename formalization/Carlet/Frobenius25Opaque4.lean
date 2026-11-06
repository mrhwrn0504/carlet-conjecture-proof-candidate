import Carlet.Frobenius25OpaqueBase
import Carlet.Frobenius25Rel1
import Carlet.Frobenius25Rel2
import Carlet.Frobenius25Rel3
import Carlet.Frobenius25Rel4
import Carlet.Frobenius25Rel5
import Carlet.Frobenius25Opaque3
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem f25_opaque_20 : f25 ∣ frobPoly 20 + r25_20 := by
  have h15 := f25_opaque_15
  have h16 : f25 ∣ frobPoly 16 + r25_16 := f25_frob_step 15 h15 f25_rel_15
  have h17 : f25 ∣ frobPoly 17 + r25_17 := f25_frob_step 16 h16 f25_rel_16
  have h18 : f25 ∣ frobPoly 18 + r25_18 := f25_frob_step 17 h17 f25_rel_17
  have h19 : f25 ∣ frobPoly 19 + r25_19 := f25_frob_step 18 h18 f25_rel_18
  have h20 : f25 ∣ frobPoly 20 + r25_20 := f25_frob_step 19 h19 f25_rel_19
  exact h20
#print axioms f25_opaque_20
