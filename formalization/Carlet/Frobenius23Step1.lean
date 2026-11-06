import Carlet.Frobenius23Rel1
import Carlet.Frobenius23Rel2
import Carlet.Frobenius23Rel3
import Carlet.Frobenius23Rel4
import Carlet.Frobenius23Base
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem f23_dvd_frob_plus_6 : f23 ∣ (X:P17)^(2^6:Nat)+r23_6 := by
  have h0 : f23 ∣ (X:P17)^(2^0:Nat)+r23_0 := by
    have hx:(X:P17)+X=0 := by have ht:=congrArg (fun z:P17=>z*X) c2_17; simpa [two_mul] using ht
    have he:(X:P17)^(2^0:Nat)+r23_0=0 := by simpa [r23_0] using hx
    rw [he]; exact dvd_zero f23
  have h1 : f23 ∣ (X:P17)^(2^1:Nat)+r23_1 := by
    have h:=f23_square_step h0 f23_rel_0
    simpa only [Xpow_square_17] using h
  have h2 : f23 ∣ (X:P17)^(2^2:Nat)+r23_2 := by
    have h:=f23_square_step h1 f23_rel_1
    simpa only [Xpow_square_17] using h
  have h3 : f23 ∣ (X:P17)^(2^3:Nat)+r23_3 := by
    have h:=f23_square_step h2 f23_rel_2
    simpa only [Xpow_square_17] using h
  have h4 : f23 ∣ (X:P17)^(2^4:Nat)+r23_4 := by
    have h:=f23_square_step h3 f23_rel_3
    simpa only [Xpow_square_17] using h
  have h5 : f23 ∣ (X:P17)^(2^5:Nat)+r23_5 := by
    have h:=f23_square_step h4 f23_rel_4
    simpa only [Xpow_square_17] using h
  have h6 : f23 ∣ (X:P17)^(2^6:Nat)+r23_6 := by
    have h:=f23_square_step h5 f23_rel_5
    simpa only [Xpow_square_17] using h
  exact h6
#print axioms f23_dvd_frob_plus_6
