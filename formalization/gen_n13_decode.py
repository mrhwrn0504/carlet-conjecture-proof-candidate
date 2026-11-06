from pathlib import Path
lines=['import Carlet.N13CodeEquivProbe','import Mathlib.Tactic','open Polynomial','noncomputable section','local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩']
for m in range(1,32):
 n=f'{m:02d}'; idx=[i for i in range(5) if m&(1<<i)]; ss='{'+','.join(map(str,idx))+'}'
 lines += [f'theorem cert13DecodeInv{n} : (cert13SubsetSum (subsetDecode13 (⟨{m}, by omega⟩ : Fin 32)))⁻¹ = AdjoinRoot.mk f13 cert13I{n} := by',f'  have hc : subsetCode13 ({ss} : Finset (Fin 5)) = (⟨{m}, by omega⟩ : Fin 32) := by', '    apply Fin.ext','    norm_num [subsetCode13, subsetCodeNat13, Finset.sum_singleton]','  rw [← hc, subsetCode13Decode_left]','  simp only [cert13SubsetSum]','  rw [cert13SubsetSum'+n+']',f'  exact (eq_inv_of_mul_eq_one_right cert13InvAdjoin{n}).symm']
lines += ['#print axioms cert13DecodeInv01','#print axioms cert13DecodeInv31']
Path('Carlet/N13DecodeInverseProbe.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
