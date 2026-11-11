import Carlet.Frobenius19Stage3a
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Polynomial
noncomputable section
theorem f19_dvd_frob_plus : f19∣(X:P19)^(2^19:Nat)+X := by
  have h16 := f19_dvd_frob_stage16
  have h17:f19∣(X:P19)^(2^17:Nat)+r17_19 := by
    have h:=square_step_19 h16 rel16_19
    simpa only [Xpow_square_19] using h
  have h18:f19∣(X:P19)^(2^18:Nat)+r18_19 := by
    have h:=square_step_19 h17 rel17_19
    simpa only [Xpow_square_19] using h
  have h19:f19∣(X:P19)^(2^19:Nat)+r19_19 := by
    have h:=square_step_19 h18 rel18_19
    simpa only [Xpow_square_19] using h
  simpa [r19_19] using h19
theorem f19_dvd_frob_sub : f19∣(X:P19)^(2^19:Nat)-X := by
  have h:=f19_dvd_frob_plus
  have hneg:-(X:P19)=X := by
    have hx:(X:P19)+X=0 := by have ht:=congrArg (fun z:P19=>z*X) c2_19; simpa [two_mul] using ht
    exact neg_eq_of_add_eq_zero_left hx
  convert h using 1 <;> simp [sub_eq_add_neg,hneg]
