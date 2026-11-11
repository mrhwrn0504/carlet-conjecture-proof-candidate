import re
from pathlib import Path
s=Path('Carlet/N11CodeEquivProbe.lean').read_text().replace('Carlet.N11SupportLinearProbe','Carlet.N13SupportLinearProbe')
for a,b in [('subsetCode','subsetCode13'),('subsetDecode','subsetDecode13'),('subsetCodeNat','subsetCodeNat13'),('subsetCodeDecode','subsetCode13Decode')]: s=s.replace(a,b)
s=re.sub(r'\bf\b','f13',s)
Path('Carlet/N13CodeEquivProbe.lean').write_text(s,encoding='utf-8')
