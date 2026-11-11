from pathlib import Path
p=Path('Carlet/N13FieldBridgeProbe.lean')
s=p.read_text()
s=s.replace('lemma f13_natDegree_bridge : f13.natDegree = 13 := by\n  have h3', '''lemma f13_natDegree_bridge : f13.natDegree = 13 := by
  have h1 : (X : P13).natDegree = 1 := Polynomial.natDegree_X
  have hplus : (X + (1 : P13)).natDegree ≤ 1 := by
    calc
      _ ≤ max (X : P13).natDegree (1 : P13).natDegree := Polynomial.natDegree_add_le _ _
      _ = 1 := by simp [h1]
  have h3''')
p.write_text(s)
