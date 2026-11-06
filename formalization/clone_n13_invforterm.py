import re
from pathlib import Path
s=Path('Carlet/N11InvForTerm.lean').read_text().replace('Carlet.N11DecodeInverseAudit','Carlet.N13DecodeInverseProbe')
for a,b in [('certSubsetSum','cert13SubsetSum'),('subsetDecode','subsetDecode13'),('certI','cert13I'),('certInvFor','cert13InvFor'),('certDecodeInv','cert13DecodeInv'),('certInvBlock','cert13InvBlock')]: s=s.replace(a,b)
s=re.sub(r'\bf\b','f13',s).replace('f_irreducible','f13_irreducible')
Path('Carlet/N13InvForTerm.lean').write_text(s,encoding='utf-8')
