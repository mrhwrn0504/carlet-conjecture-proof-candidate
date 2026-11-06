import Carlet.DistributionRecursion
import Carlet.TransferOperator

noncomputable section

namespace Carlet

/-!
The finite-field recurrence is first proved with raw cardinalities.  This
lemma isolates the normalization step: once the adjacent total counts of
subspaces containing `1` have the Gaussian-binomial ratio, the raw recurrence
becomes the probability recurrence used by Cheng.
-/

theorem normalized_recursion_from_raw_counts
    (s q A B pNext pZero weightedSum : ℝ) (twoPow : ℝ)
    (hA : A ≠ 0) (hs : s - 1 ≠ 0) (hTwoPow : twoPow ≠ 0)
    (hRatio : B / A = (q - s) / (twoPow * (s - 1)))
    (hRaw : twoPow * B * pNext =
      A * ((1 - pZero) / (s - 1) + weightedSum)) :
    (q - s) * pNext = 1 - pZero + (s - 1) * weightedSum := by
  have hCoefficient : twoPow * (B / A) = (q - s) / (s - 1) := by
    rw [hRatio]
    field_simp [hTwoPow]
  have hNormalized : twoPow * (B / A) * pNext =
      (1 - pZero) / (s - 1) + weightedSum := by
    calc
      twoPow * (B / A) * pNext = (twoPow * B * pNext) / A := by
        field_simp [hA]
      _ = (A * ((1 - pZero) / (s - 1) + weightedSum)) / A := by rw [hRaw]
      _ = _ := by field_simp [hA]
  rw [hCoefficient] at hNormalized
  have h := congrArg (fun z : ℝ => (s - 1) * z) hNormalized
  field_simp [hs] at h
  nlinarith

#print axioms normalized_recursion_from_raw_counts

end Carlet
