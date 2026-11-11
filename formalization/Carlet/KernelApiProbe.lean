import Carlet.CandidatePaper.Section31ReciprocalKernelHomogeneous
#check GradedAlgebra.toGradedRing
#check GradedAlgebra.toGradedMonoid
example : True := by
  letI := MvPolynomial.gradedAlgebra (Fin 2) (ZMod 2)
  haveI : GradedRing (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2)) := inferInstance
  trivial
