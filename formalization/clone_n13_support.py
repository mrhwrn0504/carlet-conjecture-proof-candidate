import re
from pathlib import Path
s=Path('Carlet/N11SupportLinearProbe.lean').read_text()
s=s.replace('import Carlet.N11SubsetNonzeroProbe','import Carlet.N13SubsetNonzeroProbe')
s=s.replace('import Carlet.N11FieldBridgeProbe','import Carlet.N13FieldBridgeProbe')
for a,b in [('certSubsetSum','cert13SubsetSum'),('certBase','cert13Base'),('certV','cert13V'),('certSubspace','cert13Subspace'),('certSupportEquiv','cert13SupportEquiv'),('certSupport','cert13Support'),('certIndicator','cert13Indicator')]: s=s.replace(a,b)
s=re.sub(r'\bF\b','F13',s)
s=re.sub(r'\bf\b','f13',s)
s=re.sub(r'\bf_irreducible\b','f13_irreducible',s)
Path('Carlet/N13SupportLinearProbe.lean').write_text(s,encoding='utf-8')
