import Carlet.Frobenius23Base
open Polynomial
lemma frobPoly23_eq : frobPoly 23 = (X:P17)^(2^23:Nat) := frobPoly_eq_pow 23
#print axioms frobPoly23_eq
