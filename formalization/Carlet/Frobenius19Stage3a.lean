import Carlet.Frobenius19Stage2
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Polynomial
noncomputable section
theorem f19_dvd_frob_stage16 : f19∣(X:P19)^(2^16:Nat)+r16_19 := by
  have h13 := f19_dvd_frob_stage13
  have h14:f19∣(X:P19)^(2^14:Nat)+r14_19 := by
    have h:=square_step_19 h13 rel13_19
    simpa only [Xpow_square_19] using h
  have h15:f19∣(X:P19)^(2^15:Nat)+r15_19 := by
    have h:=square_step_19 h14 rel14_19
    simpa only [Xpow_square_19] using h
  have h16:f19∣(X:P19)^(2^16:Nat)+r16_19 := by
    have h:=square_step_19 h15 rel15_19
    simpa only [Xpow_square_19] using h
  exact h16
