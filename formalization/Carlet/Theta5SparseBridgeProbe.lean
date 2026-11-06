import Carlet.Theta5Probe
import Carlet.Theta5SparseMonomial

namespace Carlet

open MvPolynomial
noncomputable section

def theta5SparsePart0 : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(4, 16)] +
  sparseXWord (R := ZMod 2) [(3, 16)] +
  sparseXWord (R := ZMod 2) [(2, 16)] +
  sparseXWord (R := ZMod 2) [(1, 16)] +
  sparseXWord (R := ZMod 2) [(0, 16)]

def theta5SparsePart1 : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(3, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(2, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(2, 8), (3, 8)] +
  sparseXWord (R := ZMod 2) [(1, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 8), (3, 8)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 8)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 8)]

def theta5SparsePart2 : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(2, 4), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(2, 4), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(2, 8), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 4), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 4), (2, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(1, 8), (2, 4), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (3, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (3, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 4), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 4)]

def theta5SparsePart3 : MvPolynomial Theta5Index (ZMod 2) :=
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
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 4), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 8), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 8), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 2), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 4), (2, 8), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 2), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 4), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 2), (3, 8)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 2), (2, 8), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 8), (2, 2), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 2), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 2), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (2, 4), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (3, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (3, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 2), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 2), (3, 4)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 4), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 4), (3, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 2), (3, 2)]

def theta5SparsePart4 : MvPolynomial Theta5Index (ZMod 2) :=
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
  sparseXWord (R := ZMod 2) [(0, 8), (1, 4), (2, 2), (3, 1), (4, 1)]

def theta5SparsePart5 : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 2), (3, 2), (4, 8)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 2), (3, 8), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 2), (2, 8), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 2), (1, 8), (2, 2), (3, 2), (4, 2)] +
  sparseXWord (R := ZMod 2) [(0, 8), (1, 2), (2, 2), (3, 2), (4, 2)]

def theta5SparsePart6 : MvPolynomial Theta5Index (ZMod 2) :=
  sparseXWord (R := ZMod 2) [(1, 4), (2, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (2, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (3, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 4), (4, 4)] +
  sparseXWord (R := ZMod 2) [(0, 4), (1, 4), (2, 4), (3, 4)]

def theta5SparsePart7 : MvPolynomial Theta5Index (ZMod 2) :=
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

def theta5SparseWordSum : MvPolynomial Theta5Index (ZMod 2) :=
  theta5SparsePart0 + theta5SparsePart1 + theta5SparsePart2 + theta5SparsePart3 +
    theta5SparsePart4 + theta5SparsePart5 + theta5SparsePart6 + theta5SparsePart7

theorem theta5_eq_sparseWordSum : theta5 = theta5SparseWordSum := by
  simp [theta5, theta5SparseWordSum, theta5SparsePart0, theta5SparsePart1,
    theta5SparsePart2, theta5SparsePart3, theta5SparsePart4, theta5SparsePart5,
    theta5SparsePart6, theta5SparsePart7, theta5Part0, theta5Part1,
    theta5Part2, theta5Part3, theta5Part4, theta5Part5, theta5Part6, theta5Part7,
    theta5X, sparseXWord, mul_assoc]

#print axioms theta5_eq_sparseWordSum

end
end Carlet
