import re
from pathlib import Path
s=Path('Carlet/N11K5SubfieldProbe.lean').read_text().replace('Carlet.N11K5CompleteProbe','Carlet.N13K5CompleteProbe')
for a,b in [('hasZeroSumSubspace_five_of_11_dvd_probe','hasZeroSumSubspace_five_of_13_dvd_probe'),('hasZeroSumSubspace_2048_probe','hasZeroSumSubspace_8192_probe'),('adjoinRoot11_card','adjoinRoot13_card')]: s=s.replace(a,b)
s=s.replace('hasZeroSumSubspace_of_algHom_probe','hasZeroSumSubspace_of_algHom13_probe')
s=re.sub(r'\bf\b','f13',s).replace('f_irreducible','f13_irreducible').replace('11','13')
Path('Carlet/N13K5SubfieldProbe.lean').write_text(s,encoding='utf-8')
