from pathlib import Path
p=Path('Carlet/N13SubsetSumProbe.lean')
lines=['import Carlet.N13ComboProbe','import Mathlib.RingTheory.AdjoinRoot','import Mathlib.Tactic','open Polynomial','noncomputable section','set_option maxHeartbeats 1000000','local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩','def cert13BasePoly : Fin 5 → P13','| 0 => cert13V01','| 1 => cert13V02','| 2 => cert13V04','| 3 => cert13V08','| 4 => cert13V16','def cert13Base (i : Fin 5) : AdjoinRoot f13 := AdjoinRoot.mk f13 (cert13BasePoly i)']
for mask in range(1,32):
    idx=[i for i in range(5) if mask & (1<<i)]
    ss='{'+','.join(map(str,idx))+'}'
    m=f'{mask:02d}'
    lines += [f'theorem cert13SubsetSum{m} : (∑ i ∈ ({ss} : Finset (Fin 5)), cert13Base i) = AdjoinRoot.mk f13 cert13V{m} := by', '  classical', '  calc', f'    _ = AdjoinRoot.mk f13 (∑ i ∈ ({ss} : Finset (Fin 5)), cert13BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm', f'    _ = AdjoinRoot.mk f13 cert13V{m} := by', f'      have hpoly : (∑ i ∈ ({ss} : Finset (Fin 5)), cert13BasePoly i) = cert13V{m} := by', '        simp [cert13BasePoly]', f'        rw [cert13Combo{m}]', '      exact congrArg (AdjoinRoot.mk f13) hpoly']
lines += ['#print axioms cert13SubsetSum01','#print axioms cert13SubsetSum31']
p.write_text('\n'.join(lines)+'\n')

