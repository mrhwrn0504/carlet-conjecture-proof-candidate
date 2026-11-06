import Carlet.Frobenius25OpaqueBase
import Carlet.Frobenius25Rel1
import Carlet.Frobenius25Rel2
import Carlet.Frobenius25Rel3
import Carlet.Frobenius25Rel4
import Carlet.Frobenius25Rel5
import Carlet.Frobenius25Opaque4
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem f25_opaque_25 : f25 ∣ frobPoly 25 + r25_25 := by
  have h20 := f25_opaque_20
  have h21 : f25 ∣ frobPoly 21 + r25_21 := f25_frob_step 20 h20 f25_rel_20
  have h22 : f25 ∣ frobPoly 22 + r25_22 := f25_frob_step 21 h21 f25_rel_21
  have h23 : f25 ∣ frobPoly 23 + r25_23 := f25_frob_step 22 h22 f25_rel_22
  have h24 : f25 ∣ frobPoly 24 + r25_24 := f25_frob_step 23 h23 f25_rel_23
  have h25 : f25 ∣ frobPoly 25 + r25_25 := f25_frob_step 24 h24 f25_rel_24
  exact h25
#print axioms f25_opaque_25
