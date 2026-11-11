import Carlet.Theta5Probe
import Carlet.Theta5EvaluationStagesProbe
import Carlet.Theta5SparseMonomial
import Carlet.Theta5SparseBridgeProbe

noncomputable section
namespace Carlet
open MvPolynomial


def theta5LastZero : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(3, 16)] +
  sparseXWord (R := ZMod 2) [(2, 16)] +
  sparseXWord (R := ZMod 2) [(1, 16)] +
  sparseXWord (R := ZMod 2) [(0, 16)] +
  sparseXWord (R := ZMod 2) [(2, 8), (3, 8)] +
  sparseXWord (R := ZMod 2) [(1, 8), (3, 8)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 4), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 4), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 2), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 8), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 2), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 4), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 2), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 8), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 2), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 2), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 4), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 2), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 4), (3, 4)]

def theta5LastPositive : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(4, 16)] +
  sparseXWord (R := ZMod 2) [(3, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(2, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(2, 4), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(2, 4), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(2, 8), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 4), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 2), (2, 2), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 2), (2, 2), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 2), (2, 4), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 2), (2, 4), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(1, 2), (2, 8), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 2), (2, 8), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 2), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 2), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 4), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (2, 2), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (2, 2), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (2, 4), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (2, 4), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (2, 8), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (2, 8), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 2), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 2), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 4), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 1), (2, 2), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 1), (2, 2), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 1), (2, 4), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 1), (2, 4), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 1), (2, 8), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 1), (2, 8), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 2), (2, 1), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 2), (2, 1), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 2), (2, 4), (3, 1), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 2), (2, 4), (3, 8), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 2), (2, 8), (3, 1), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 2), (2, 8), (3, 4), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 4), (2, 1), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 4), (2, 1), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 4), (2, 2), (3, 1), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 4), (2, 2), (3, 8), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 4), (2, 8), (3, 1), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 4), (2, 8), (3, 2), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 8), (2, 1), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 8), (2, 1), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 8), (2, 2), (3, 1), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 8), (2, 2), (3, 4), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 8), (2, 4), (3, 1), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 1), (1, 8), (2, 4), (3, 2), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 1), (2, 1), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 1), (2, 1), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 1), (2, 4), (3, 1), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 1), (2, 4), (3, 8), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 1), (2, 8), (3, 1), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 1), (2, 8), (3, 4), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 1), (3, 1), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 1), (3, 8), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 8), (3, 1), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 1), (3, 1), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 1), (3, 4), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 4), (3, 1), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 1), (2, 1), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 1), (2, 1), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 1), (2, 2), (3, 1), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 1), (2, 2), (3, 8), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 1), (2, 8), (3, 1), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 1), (2, 8), (3, 2), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 1), (3, 1), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 1), (3, 8), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 8), (3, 1), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 1), (3, 1), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 1), (3, 2), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 2), (3, 1), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 1), (2, 1), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 1), (2, 1), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 1), (2, 2), (3, 1), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 1), (2, 2), (3, 4), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 1), (2, 4), (3, 1), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 1), (2, 4), (3, 2), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 1), (3, 1), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 1), (3, 4), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 4), (3, 1), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 1), (3, 1), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 1), (3, 2), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 2), (3, 1), (4, 1)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 2), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 2), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 2), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 4), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 4), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 2), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 4), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 4), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 2), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 2), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 4), (3, 2), (4, 2)]

theorem theta5_eq_last_split : theta5 = theta5LastZero + theta5LastPositive := by
  rw [theta5_eq_sparseWordSum]
  simp only [theta5SparseWordSum, theta5SparsePart0, theta5SparsePart1,
    theta5SparsePart2, theta5SparsePart3, theta5SparsePart4, theta5SparsePart5,
    theta5SparsePart6, theta5SparsePart7, theta5LastZero, theta5LastPositive]
  abel

#print axioms theta5_eq_last_split

end Carlet
end
