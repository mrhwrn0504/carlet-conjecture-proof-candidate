import re
from pathlib import Path
s=Path('Carlet/N13SubsetSumProbe.lean').read_text()
s=s.replace('Carlet.N13ComboProbe','Carlet.N11ComboProbe')
for a,b in [('cert13SubsetSum','certSubsetSum'),('cert13BasePoly','certBasePoly'),('cert13Base','certBase'),('cert13Combo','certCombo'),('cert13V','certV'),('P13','P'),('f13_irreducible','f_irreducible')]: s=s.replace(a,b)
s=re.sub(r'\bf13\b','f',s)
s=s.replace('f13_irreducible','f_irreducible')
Path('Carlet/N11SubsetSumProbe.lean').write_text(s,encoding='utf-8')
