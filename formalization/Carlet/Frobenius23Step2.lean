import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Step1
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_12 : f23 ∣ (X:P17)^(2^12:Nat)+r23_12 := by
  have h6 := f23_dvd_frob_plus_6
  have h7 : f23 ∣ (X:P17)^(2^7:Nat)+r23_7 := by
    have h:=f23_square_step h6 f23_rel_6
    simpa only [Xpow_square_17] using h
  have h8 : f23 ∣ (X:P17)^(2^8:Nat)+r23_8 := by
    have h:=f23_square_step h7 f23_rel_7
    simpa only [Xpow_square_17] using h
  have h9 : f23 ∣ (X:P17)^(2^9:Nat)+r23_9 := by
    have h:=f23_square_step h8 f23_rel_8
    simpa only [Xpow_square_17] using h
  have h10 : f23 ∣ (X:P17)^(2^10:Nat)+r23_10 := by
    have h:=f23_square_step h9 f23_rel_9
    simpa only [Xpow_square_17] using h
  have h11 : f23 ∣ (X:P17)^(2^11:Nat)+r23_11 := by
    have h:=f23_square_step h10 f23_rel_10
    simpa only [Xpow_square_17] using h
  have h12 : f23 ∣ (X:P17)^(2^12:Nat)+r23_12 := by
    have h:=f23_square_step h11 f23_rel_11
    simpa only [Xpow_square_17] using h
  exact h12
#print axioms f23_dvd_frob_plus_12
