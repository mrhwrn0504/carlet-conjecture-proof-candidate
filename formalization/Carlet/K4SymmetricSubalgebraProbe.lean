import Carlet.K4ThetaQuadraticIrreducibilityProbe
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Tactic

noncomputable section
namespace Carlet

variable (K : Type*) [Field K] [CharP K 2]

/-- Formal order: X0 represents s4, and X1,X2,X3 represent s1,s2,s3. -/
def k4FormalSymmetricPolynomial : MvPolynomial (Fin 4) K :=
  MvPolynomial.X 0 ^ 2 +
    MvPolynomial.X 1 * (MvPolynomial.X 1 * MvPolynomial.X 2 + MvPolynomial.X 3) *
      MvPolynomial.X 0 +
    (MvPolynomial.X 1 ^ 4 + MvPolynomial.X 2 ^ 2 + MvPolynomial.X 1 * MvPolynomial.X 3) ^ 2

omit [CharP K 2] in
theorem k4FormalSymmetricPolynomial_equiv :
    (MvPolynomial.finSuccEquiv K 3) (k4FormalSymmetricPolynomial K) = k4ThetaQuadratic K := by
  have h1 : (MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X (1 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 3)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 3) (j := (0 : Fin 3)))
  have h2 : (MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X (2 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 3)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 3) (j := (1 : Fin 3)))
  have h3 : (MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X (3 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 3)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 3) (j := (2 : Fin 3)))
  simp [k4FormalSymmetricPolynomial, k4ThetaQuadratic, k4ConstantA, k4ConstantB,
    MvPolynomial.finSuccEquiv_X_zero, h1, h2, h3]

theorem k4FormalSymmetricPolynomial_irreducible :
    Irreducible (k4FormalSymmetricPolynomial K) := by
  have h := Irreducible.map (MvPolynomial.finSuccEquiv K 3).symm
    (k4ThetaQuadratic_irreducible K)
  have hback : (MvPolynomial.finSuccEquiv K 3).symm (k4ThetaQuadratic K) =
      k4FormalSymmetricPolynomial K := by
    rw [← k4FormalSymmetricPolynomial_equiv K]
    exact (MvPolynomial.finSuccEquiv K 3).symm_apply_apply _
  simpa [hback] using h

/-- Rename X0,X1,X2,X3 to the standard symmetric-coordinate order s4,s1,s2,s3. -/
def k4SymmetricPermutation : Equiv.Perm (Fin 4) :=
  ((Equiv.swap 0 3).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 1)

def k4SymmetricRingEquiv : MvPolynomial (Fin 4) K ≃ₐ[K]
    MvPolynomial.symmetricSubalgebra (Fin 4) K :=
  (MvPolynomial.renameEquiv K k4SymmetricPermutation).trans
    (MvPolynomial.esymmAlgEquiv (Fin 4) K (by simp))

def k4ThetaSymmetricElement : MvPolynomial.symmetricSubalgebra (Fin 4) K :=
  k4SymmetricRingEquiv K (k4FormalSymmetricPolynomial K)

omit [CharP K 2] in
theorem k4ThetaSymmetricElement_coe :
    (k4ThetaSymmetricElement K : MvPolynomial (Fin 4) K) =
      (MvPolynomial.esymm (Fin 4) K 4) ^ 2 +
        (MvPolynomial.esymm (Fin 4) K 1) *
          ((MvPolynomial.esymm (Fin 4) K 1) * (MvPolynomial.esymm (Fin 4) K 2) +
            (MvPolynomial.esymm (Fin 4) K 3)) * (MvPolynomial.esymm (Fin 4) K 4) +
        ((MvPolynomial.esymm (Fin 4) K 1) ^ 4 + (MvPolynomial.esymm (Fin 4) K 2) ^ 2 +
          (MvPolynomial.esymm (Fin 4) K 1) * (MvPolynomial.esymm (Fin 4) K 3)) ^ 2 := by
  simp [k4ThetaSymmetricElement, k4SymmetricRingEquiv, k4FormalSymmetricPolynomial,
    k4SymmetricPermutation, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    MvPolynomial.esymmAlgEquiv_apply, MvPolynomial.esymmAlgHom_apply, Equiv.swap_apply_def]

theorem k4ThetaSymmetricElement_irreducible :
    Irreducible (k4ThetaSymmetricElement K) := by
  exact Irreducible.map (k4SymmetricRingEquiv K) (k4FormalSymmetricPolynomial_irreducible K)

#print axioms k4FormalSymmetricPolynomial_irreducible
#print axioms k4ThetaSymmetricElement_coe
#print axioms k4ThetaSymmetricElement_irreducible
end Carlet
