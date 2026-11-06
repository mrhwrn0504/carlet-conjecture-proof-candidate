from pathlib import Path
p=Path('Carlet/RemainingCases13.lean')
s=p.read_text()
s=s.replace('/-- Residual ranges after also closing the k=5 family 13 | n. -/', '''theorem hasZeroSumSubspace_five_of_13_dvd_card {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] (n : ℕ) (hcard : Fintype.card K = 2 ^ n)
    (hdiv : 13 ∣ n) : HasZeroSumSubspace K 5 := by
  exact hasZeroSumSubspace_five_of_13_dvd_probe n (finrank_eq_of_card n hcard) hdiv

/-- Residual ranges after also closing the k=5 family 13 | n. -/''')
s=s.replace('Or.inr ⟨hk, h5, h11, h21, h31⟩','Or.inr ⟨hk, h5, h11, not hdiv13, h21, h31⟩')
p.write_text(s)
