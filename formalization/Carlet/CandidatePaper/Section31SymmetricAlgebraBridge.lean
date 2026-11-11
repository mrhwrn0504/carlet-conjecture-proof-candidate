import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Carlet.CandidatePaper.ReciprocalCoordinates

/-! Exact coordinate identification of the symmetric algebra in the supplied
paper with the polynomial model used by the reciprocal-coordinate development. -/

noncomputable section
namespace Carlet.CandidatePaper.Section31SymmetricAlgebraBridge

open Carlet.CandidatePaper.ReciprocalCoordinates

abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2

def symmetricPolynomialEquiv (n : ℕ) :
    SymmetricAlgebra (ZMod 2) (BinaryVector n) ≃ₐ[ZMod 2]
      MvPolynomial (Fin n) (ZMod 2) :=
  SymmetricAlgebra.equivMvPolynomial (Pi.basisFun (ZMod 2) (Fin n))

theorem symmetricAlgebra_vector_eq_linearForm (n : ℕ) (v : BinaryVector n) :
    symmetricPolynomialEquiv n (SymmetricAlgebra.ι (ZMod 2) (BinaryVector n) v) =
      linearForm n v := by
  let b := Pi.basisFun (ZMod 2) (Fin n)
  have hrepr : (∑ i : Fin n, b.repr v i • b i) = v := b.sum_repr v
  conv_lhs => rw [← hrepr]
  unfold linearForm
  simp only [map_sum, map_smul, symmetricPolynomialEquiv]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [Algebra.smul_def, MvPolynomial.C_eq_algebraMap]
  simp [b, Pi.basisFun_repr]

theorem symmetricPolynomialEquiv_injective (n : ℕ) :
    Function.Injective (symmetricPolynomialEquiv n) :=
  (symmetricPolynomialEquiv n).injective

#print axioms symmetricAlgebra_vector_eq_linearForm
#print axioms symmetricPolynomialEquiv_injective

end Carlet.CandidatePaper.Section31SymmetricAlgebraBridge
