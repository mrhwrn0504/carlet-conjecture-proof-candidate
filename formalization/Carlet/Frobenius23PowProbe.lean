import Carlet.Frobenius17Probe
open Polynomial
noncomputable section
set_option maxRecDepth 524288
set_option maxHeartbeats 4000000
theorem test_pow_17 : ((X:P17)^(2^17:Nat))^2=(X:P17)^(2^18:Nat) := Xpow_square_17 17
#print axioms test_pow_17
