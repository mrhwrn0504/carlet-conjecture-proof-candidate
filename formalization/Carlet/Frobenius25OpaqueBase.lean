import Carlet.Frobenius25Base
import Carlet.Frobenius23Base
open Polynomial
noncomputable section

theorem f25_frob_step (m : Nat) {r s q : P17}
    (h : f25 ∣ frobPoly m + r) (hr : r^2+s=f25*q) :
    f25 ∣ frobPoly (m+1) + s := by
  have hs := f25_square_step h hr
  have hp : (frobPoly m)^2 = frobPoly (m+1) := (frobPoly_succ m).symm
  exact (congrArg (fun z : P17 => f25 ∣ z+s) hp).mp hs

#print axioms f25_frob_step
