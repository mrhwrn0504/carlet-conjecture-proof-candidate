import Carlet.K4ThetaAbsoluteIrreducibleProbe
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Carlet

theorem theta4_isHomogeneous : theta4.IsHomogeneous 8 := by
  have h0 : (k4X 0 ^ 8).IsHomogeneous 8 := by
    simpa [k4X] using (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 8)
  have h1 : (k4X 1 ^ 8).IsHomogeneous 8 := by
    simpa [k4X] using (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 8)
  have h2 : (k4X 2 ^ 8).IsHomogeneous 8 := by
    simpa [k4X] using (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 8)
  have h3 : (k4X 3 ^ 8).IsHomogeneous 8 := by
    simpa [k4X] using (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 8)
  have h4 : (k4X 0 ^ 4 * k4X 1 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using ((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4))
  have h5 : (k4X 0 ^ 4 * k4X 2 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using ((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4))
  have h6 : (k4X 0 ^ 4 * k4X 3 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using ((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4))
  have h7 : (k4X 1 ^ 4 * k4X 2 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using ((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4))
  have h8 : (k4X 1 ^ 4 * k4X 3 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using ((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4))
  have h9 : (k4X 2 ^ 4 * k4X 3 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using ((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4))
  have h10 : (k4X 1 ^ 4 * k4X 2 ^ 2 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  have h11 : (k4X 1 ^ 2 * k4X 2 ^ 4 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  have h12 : (k4X 1 ^ 2 * k4X 2 ^ 2 * k4X 3 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4))
  have h13 : (k4X 0 ^ 4 * k4X 2 ^ 2 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  have h14 : (k4X 0 ^ 2 * k4X 2 ^ 4 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  have h15 : (k4X 0 ^ 2 * k4X 2 ^ 2 * k4X 3 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4))
  have h16 : (k4X 0 ^ 4 * k4X 1 ^ 2 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  have h17 : (k4X 0 ^ 2 * k4X 1 ^ 4 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  have h18 : (k4X 0 ^ 2 * k4X 1 ^ 2 * k4X 3 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4))
  have h19 : (k4X 0 ^ 4 * k4X 1 ^ 2 * k4X 2 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2))
  have h20 : (k4X 0 ^ 2 * k4X 1 ^ 4 * k4X 2 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2))
  have h21 : (k4X 0 ^ 2 * k4X 1 ^ 2 * k4X 2 ^ 4).IsHomogeneous 8 := by
    simpa [k4X] using (((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4))
  have h22 : (k4X 0 ^ 4 * k4X 1 ^ 2 * k4X 2 * k4X 3).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (2 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (3 : Fin 4)))
  have h23 : (k4X 0 ^ 4 * k4X 2 ^ 2 * k4X 1 * k4X 3).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (1 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (3 : Fin 4)))
  have h24 : (k4X 0 ^ 4 * k4X 3 ^ 2 * k4X 1 * k4X 2).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (1 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (2 : Fin 4)))
  have h25 : (k4X 1 ^ 4 * k4X 0 ^ 2 * k4X 2 * k4X 3).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (2 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (3 : Fin 4)))
  have h26 : (k4X 1 ^ 4 * k4X 2 ^ 2 * k4X 0 * k4X 3).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (0 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (3 : Fin 4)))
  have h27 : (k4X 1 ^ 4 * k4X 3 ^ 2 * k4X 0 * k4X 2).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (0 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (2 : Fin 4)))
  have h28 : (k4X 2 ^ 4 * k4X 0 ^ 2 * k4X 1 * k4X 3).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (1 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (3 : Fin 4)))
  have h29 : (k4X 2 ^ 4 * k4X 1 ^ 2 * k4X 0 * k4X 3).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (0 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (3 : Fin 4)))
  have h30 : (k4X 2 ^ 4 * k4X 3 ^ 2 * k4X 0 * k4X 1).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (0 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (1 : Fin 4)))
  have h31 : (k4X 3 ^ 4 * k4X 0 ^ 2 * k4X 1 * k4X 2).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (1 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (2 : Fin 4)))
  have h32 : (k4X 3 ^ 4 * k4X 1 ^ 2 * k4X 0 * k4X 2).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (0 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (2 : Fin 4)))
  have h33 : (k4X 3 ^ 4 * k4X 2 ^ 2 * k4X 0 * k4X 1).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 4).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (0 : Fin 4))).mul (MvPolynomial.isHomogeneous_X (R := ZMod 2) (1 : Fin 4)))
  have h34 : (k4X 0 ^ 2 * k4X 1 ^ 2 * k4X 2 ^ 2 * k4X 3 ^ 2).IsHomogeneous 8 := by
    simpa [k4X] using ((((MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (0 : Fin 4) 2).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (1 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (2 : Fin 4) 2)).mul (MvPolynomial.isHomogeneous_X_pow (R := ZMod 2) (3 : Fin 4) 2))
  simpa only [theta4] using ((((((((((((((((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21).add h22).add h23).add h24).add h25).add h26).add h27).add h28).add h29).add h30).add h31).add h32).add h33).add h34)

theorem k4ThetaOver_isHomogeneous (K : Type*) [Field K] [Algebra (ZMod 2) K] :
    (k4ThetaOver K).IsHomogeneous 8 := by
  exact theta4_isHomogeneous.map (algebraMap (ZMod 2) K)

theorem k4ThetaOver_totalDegree (K : Type*) [Field K] [Algebra (ZMod 2) K] :
    (k4ThetaOver K).totalDegree = 8 :=
  (k4ThetaOver_isHomogeneous K).totalDegree (k4ThetaOver_ne_zero K)

#print axioms theta4_isHomogeneous
#print axioms k4ThetaOver_totalDegree
end Carlet
