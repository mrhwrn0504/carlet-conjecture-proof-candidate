from pathlib import Path
lines=['import Carlet.N13SubsetSumProbe','import Mathlib.Tactic','noncomputable section','lemma mul_eq_one_left_ne_zero13 {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by','  intro ha','  rw [ha, zero_mul] at h','  exact zero_ne_one h']
for m in range(1,32):
  n=f'{m:02d}'; idx=[i for i in range(5) if m&(1<<i)]; ss='{'+','.join(map(str,idx))+'}'
  lines += [f'theorem cert13V{n}_nonzero : AdjoinRoot.mk f13 cert13V{n} ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin{n}',f'theorem cert13SubsetSum{n}_nonzero : (∑ j ∈ ({ss} : Finset (Fin 5)), cert13Base j) ≠ 0 := by','  rw [cert13SubsetSum'+n+']','  exact cert13V'+n+'_nonzero']
lines += ['#print axioms cert13SubsetSum01_nonzero','#print axioms cert13SubsetSum31_nonzero']
Path('Carlet/N13SubsetNonzeroProbe.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
