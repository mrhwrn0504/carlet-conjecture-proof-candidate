import Carlet.N17N19InverseProbe
import Carlet.F19NamedIrreducible
open Polynomial
noncomputable section

theorem f19_certificate_eq_frobenius : f19 = f19Frob := by
  unfold f19 f19Frob
  ring

theorem f19_certificate_irreducible : Irreducible f19 := by
  rw [f19_certificate_eq_frobenius]
  exact f19_irreducible

#print axioms f19_certificate_eq_frobenius
#print axioms f19_certificate_irreducible
