import Carlet.Frobenius25OpaqueBase
import Carlet.Frobenius25Rel1
import Carlet.Frobenius25Rel2
import Carlet.Frobenius25Rel3
import Carlet.Frobenius25Rel4
import Carlet.Frobenius25Rel5
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem f25_opaque_5 : f25 ∣ frobPoly 5 + r25_5 := by
  have h0 : f25 ∣ frobPoly 0 + r25_0 := by
    rw [frobPoly_zero]
    have hx : (X:P17)+X=0 := by
      have ht := congrArg (fun z : P17 => z*X) c2_17
      simpa [two_mul] using ht
    simp [r25_0, hx]
  have h1 : f25 ∣ frobPoly 1 + r25_1 := f25_frob_step 0 h0 f25_rel_0
  have h2 : f25 ∣ frobPoly 2 + r25_2 := f25_frob_step 1 h1 f25_rel_1
  have h3 : f25 ∣ frobPoly 3 + r25_3 := f25_frob_step 2 h2 f25_rel_2
  have h4 : f25 ∣ frobPoly 4 + r25_4 := f25_frob_step 3 h3 f25_rel_3
  have h5 : f25 ∣ frobPoly 5 + r25_5 := f25_frob_step 4 h4 f25_rel_4
  exact h5
#print axioms f25_opaque_5
