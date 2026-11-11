import Carlet.Frobenius19Stage1
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Polynomial
noncomputable section
theorem f19_dvd_frob_stage13 : f19∣(X:P19)^(2^13:Nat)+r13_19 := by
  have h7 := f19_dvd_frob_stage7
  have h8:f19∣(X:P19)^(2^8:Nat)+r8_19 := by
    have h:=square_step_19 h7 rel7_19
    simpa only [Xpow_square_19] using h
  have h9:f19∣(X:P19)^(2^9:Nat)+r9_19 := by
    have h:=square_step_19 h8 rel8_19
    simpa only [Xpow_square_19] using h
  have h10:f19∣(X:P19)^(2^10:Nat)+r10_19 := by
    have h:=square_step_19 h9 rel9_19
    simpa only [Xpow_square_19] using h
  have h11:f19∣(X:P19)^(2^11:Nat)+r11_19 := by
    have h:=square_step_19 h10 rel10_19
    simpa only [Xpow_square_19] using h
  have h12:f19∣(X:P19)^(2^12:Nat)+r12_19 := by
    have h:=square_step_19 h11 rel11_19
    simpa only [Xpow_square_19] using h
  have h13:f19∣(X:P19)^(2^13:Nat)+r13_19 := by
    have h:=square_step_19 h12 rel12_19
    simpa only [Xpow_square_19] using h
  exact h13
