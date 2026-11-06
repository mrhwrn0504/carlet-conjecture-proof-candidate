import Carlet.F19NamedIter
open Polynomial
noncomputable section
set_option maxRecDepth 16384

lemma f19_iter_bridge (n : Nat) (h : f19Frob ∣ iterFrob19 n + X) :
    f19Frob ∣ (X:P19Frob)^(2^n) + X := by
  exact (congrArg (fun x : P19Frob => f19Frob ∣ x + X) (iterFrob19_eq n)).mp h

theorem f19_dvd_frob_iter_plus : f19Frob ∣ (X:P19Frob)^(2^19:Nat)+X :=
  f19_iter_bridge 19 f19_dvd_iterFrob

#print axioms f19_dvd_frob_iter_plus
