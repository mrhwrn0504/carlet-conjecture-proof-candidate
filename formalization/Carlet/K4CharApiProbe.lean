import Carlet.K4CoeffRecursionProbe
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
#synth CharP (ZMod 2) 2
#synth CharP Carlet.K4FreeRing 2
#synth ExpChar Carlet.K4FreeRing 2
#check charP_of_injective_algebraMap
#check MvPolynomial.C_injective
#check MvPolynomial.charP
