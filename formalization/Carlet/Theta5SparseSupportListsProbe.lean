import Carlet.Theta5LastCoordinateExpansionProbe
import Mathlib.Tactic

noncomputable section
namespace Carlet

/-- The 35 monomials in the last-coordinate-zero part of Θ₅. -/
def theta5LastZeroWordList : List (List (Fin 5 × ℕ) × ZMod 2) := [
  ([((3 : Fin 5), 16)], (1 : ZMod 2)),
  ([((2 : Fin 5), 16)], (1 : ZMod 2)),
  ([((1 : Fin 5), 16)], (1 : ZMod 2)),
  ([((0 : Fin 5), 16)], (1 : ZMod 2)),
  ([((2 : Fin 5), 8), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((1 : Fin 5), 8), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((1 : Fin 5), 8), ((2 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((2 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((1 : Fin 5), 8)], (1 : ZMod 2)),
  ([((1 : Fin 5), 4), ((2 : Fin 5), 4), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((1 : Fin 5), 4), ((2 : Fin 5), 8), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((1 : Fin 5), 8), ((2 : Fin 5), 4), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((2 : Fin 5), 4), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((2 : Fin 5), 8), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 4), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 4), ((2 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 8), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 8), ((2 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((2 : Fin 5), 4), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((1 : Fin 5), 4), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((1 : Fin 5), 4), ((2 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 2), ((1 : Fin 5), 2), ((2 : Fin 5), 4), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 2), ((1 : Fin 5), 2), ((2 : Fin 5), 8), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 2), ((1 : Fin 5), 4), ((2 : Fin 5), 2), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 2), ((1 : Fin 5), 4), ((2 : Fin 5), 8), ((3 : Fin 5), 2)], (1 : ZMod 2)),
  ([((0 : Fin 5), 2), ((1 : Fin 5), 8), ((2 : Fin 5), 2), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 2), ((1 : Fin 5), 8), ((2 : Fin 5), 4), ((3 : Fin 5), 2)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 2), ((2 : Fin 5), 2), ((3 : Fin 5), 8)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 2), ((2 : Fin 5), 8), ((3 : Fin 5), 2)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 8), ((2 : Fin 5), 2), ((3 : Fin 5), 2)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((1 : Fin 5), 2), ((2 : Fin 5), 2), ((3 : Fin 5), 4)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((1 : Fin 5), 2), ((2 : Fin 5), 4), ((3 : Fin 5), 2)], (1 : ZMod 2)),
  ([((0 : Fin 5), 8), ((1 : Fin 5), 4), ((2 : Fin 5), 2), ((3 : Fin 5), 2)], (1 : ZMod 2)),
  ([((0 : Fin 5), 4), ((1 : Fin 5), 4), ((2 : Fin 5), 4), ((3 : Fin 5), 4)], (1 : ZMod 2))
]

theorem theta5LastZero_eq_weightedWordsSum :
    theta5LastZero = sparseXWeightedWordsSum (R := ZMod 2) theta5LastZeroWordList := by
  simp [theta5LastZero, theta5LastZeroWordList, sparseXWeightedWordsSum, sparseXWord]
  abel

theorem coeff_theta5LastZero (e : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff e theta5LastZero =
      theta5LastZeroWordList.foldr (fun item acc =>
        (if sparseXWordExponent item.1 = e then item.2 else 0) + acc) 0 := by
  rw [theta5LastZero_eq_weightedWordsSum]
  exact coeff_sparseXWeightedWordsSum theta5LastZeroWordList e
theorem theta5LastZeroWordList_length : theta5LastZeroWordList.length = 35 := by
  decide

theorem theta5LastZeroWordList_nodup : theta5LastZeroWordList.Nodup := by
  decide
#print axioms theta5LastZero_eq_weightedWordsSum
#print axioms coeff_theta5LastZero
#print axioms theta5LastZeroWordList_length
#print axioms theta5LastZeroWordList_nodup

end Carlet


