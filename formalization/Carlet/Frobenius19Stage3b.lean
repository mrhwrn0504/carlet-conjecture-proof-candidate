import Carlet.Frobenius19Stage3a
set_option maxRecDepth 1048576
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Polynomial
noncomputable section
theorem f19_dvd_frob_stage17 : f19∣(X:P19)^(2^17:Nat)+r17_19 := by
  have h16 := f19_dvd_frob_stage16
  have h17:f19∣(X:P19)^(2^17:Nat)+r17_19 := by
    have h:=square_step_19 h16 rel16_19
    simpa only [Xpow_square_19] using h
  exact h17

