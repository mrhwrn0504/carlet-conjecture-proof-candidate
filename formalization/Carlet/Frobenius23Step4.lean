import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Step3
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_23 : f23 ∣ (X:P17)^(2^23:Nat)+r23_23 := by
  have h18 := f23_dvd_frob_plus_18
  have h19 : f23 ∣ (X:P17)^(2^19:Nat)+r23_19 := by
    have h:=f23_square_step h18 f23_rel_18
    simpa only [Xpow_square_17] using h
  have h20 : f23 ∣ (X:P17)^(2^20:Nat)+r23_20 := by
    have h:=f23_square_step h19 f23_rel_19
    simpa only [Xpow_square_17] using h
  have h21 : f23 ∣ (X:P17)^(2^21:Nat)+r23_21 := by
    have h:=f23_square_step h20 f23_rel_20
    simpa only [Xpow_square_17] using h
  have h22 : f23 ∣ (X:P17)^(2^22:Nat)+r23_22 := by
    have h:=f23_square_step h21 f23_rel_21
    simpa only [Xpow_square_17] using h
  have h23 : f23 ∣ (X:P17)^(2^23:Nat)+r23_23 := by
    have h:=f23_square_step h22 f23_rel_22
    simpa only [Xpow_square_17] using h
  exact h23
#print axioms f23_dvd_frob_plus_23
