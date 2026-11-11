import re
from pathlib import Path
s=Path('Carlet/N11K5CompleteProbe.lean').read_text().replace('Carlet.N11InvForTerm','Carlet.N13InvForTerm').replace('Carlet.N11FieldBridgeProbe','Carlet.N13FieldBridgeProbe')
for a,b in [('hasZeroSumSubspace_2048_probe','hasZeroSumSubspace_8192_probe'),('hasZeroSumSubspace_n11_card_probe','hasZeroSumSubspace_n13_card_probe'),('certSubsetSum','cert13SubsetSum'),('certSubspace','cert13Subspace'),('certInvFor','cert13InvFor'),('certDecodeInvSucc','cert13DecodeInvSucc'),('subsetCodeEquiv','subsetCode13Equiv'),('subsetDecode','subsetDecode13'),('adjoinRoot11_card','adjoinRoot13_card'),('certSubsetSum_empty','cert13SubsetSum_empty'),('certSubsetSum_all_inverse_zero','cert13SubsetSum_all_inverse_zero'),('certSubspace_isZeroSum_probe','cert13Subspace_isZeroSum_probe')]: s=s.replace(a,b)
s=s.replace('cert13InvFor_sum_zero','cert13InvFor_sum_zero')
s=re.sub(r'\bf\b','f13',s).replace('f_irreducible','f13_irreducible')
s=s.replace('2 ^ 11','2 ^ 13')
Path('Carlet/N13K5CompleteProbe.lean').write_text(s,encoding='utf-8')
