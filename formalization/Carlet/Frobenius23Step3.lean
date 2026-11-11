import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Step2
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_18 : f23 ∣ (X:P17)^(2^18:Nat)+r23_18 := by
  have h12 := f23_dvd_frob_plus_12
  have h13 : f23 ∣ (X:P17)^(2^13:Nat)+r23_13 := by
    have h:=f23_square_step h12 f23_rel_12
    simpa only [Xpow_square_17] using h
  have h14 : f23 ∣ (X:P17)^(2^14:Nat)+r23_14 := by
    have h:=f23_square_step h13 f23_rel_13
    simpa only [Xpow_square_17] using h
  have h15 : f23 ∣ (X:P17)^(2^15:Nat)+r23_15 := by
    have h:=f23_square_step h14 f23_rel_14
    simpa only [Xpow_square_17] using h
  have h16 : f23 ∣ (X:P17)^(2^16:Nat)+r23_16 := by
    have h:=f23_square_step h15 f23_rel_15
    simpa only [Xpow_square_17] using h
  have h17 : f23 ∣ (X:P17)^(2^17:Nat)+r23_17 := by
    have h:=f23_square_step h16 f23_rel_16
    simpa only [Xpow_square_17] using h
  have h18 : f23 ∣ (X:P17)^(2^18:Nat)+r23_18 := by
    have h:=f23_square_step h17 f23_rel_17
    simpa only [Xpow_square_17] using h
  exact h18
#print axioms f23_dvd_frob_plus_18
