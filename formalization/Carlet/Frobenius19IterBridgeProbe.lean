import Carlet.Frobenius19IterProbe
open Polynomial
noncomputable section
set_option maxRecDepth 16384

lemma f19_iter_bridge (n : Nat) (h : f19 ∣ iterFrob19 n + X) :
    f19 ∣ (X:P19)^(2^n) + X := by
  exact (congrArg (fun x : P19 => f19 ∣ x + X) (iterFrob19_eq n)).mp h

theorem f19_dvd_frob_iter_plus : f19 ∣ (X:P19)^(2^19:Nat)+X :=
  f19_iter_bridge 19 f19_dvd_iterFrob

#print axioms f19_dvd_frob_iter_plus
