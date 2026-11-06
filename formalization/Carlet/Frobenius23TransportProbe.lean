import Carlet.Frobenius23Pow23Probe
open Polynomial
noncomputable section
example (h : f23 ∣ frobPoly 23 + (X:P17)) : f23 ∣ (X:P17)^(2^23:Nat) + X := by
  exact (congrArg (fun z:P17 => f23 ∣ z + X) frobPoly23_eq).mp h
