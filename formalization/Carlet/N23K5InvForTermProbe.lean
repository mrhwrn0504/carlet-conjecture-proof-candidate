import Carlet.N23K5DecodeInverseProbe
import Carlet.N23K5InverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩
def n23K5InvFor (i : Fin 31) : AdjoinRoot f23 := AdjoinRoot.mk f23 (match i.val with
  | 0 => n23K5I01
  | 1 => n23K5I02
  | 2 => n23K5I03
  | 3 => n23K5I04
  | 4 => n23K5I05
  | 5 => n23K5I06
  | 6 => n23K5I07
  | 7 => n23K5I08
  | 8 => n23K5I09
  | 9 => n23K5I10
  | 10 => n23K5I11
  | 11 => n23K5I12
  | 12 => n23K5I13
  | 13 => n23K5I14
  | 14 => n23K5I15
  | 15 => n23K5I16
  | 16 => n23K5I17
  | 17 => n23K5I18
  | 18 => n23K5I19
  | 19 => n23K5I20
  | 20 => n23K5I21
  | 21 => n23K5I22
  | 22 => n23K5I23
  | 23 => n23K5I24
  | 24 => n23K5I25
  | 25 => n23K5I26
  | 26 => n23K5I27
  | 27 => n23K5I28
  | 28 => n23K5I29
  | 29 => n23K5I30
  | 30 => n23K5I31
  | _ => 0)
theorem n23K5DecodeInvSucc (i : Fin 31) : (n23K5SubsetSum (n23K5SubsetDecode i.succ))⁻¹ = n23K5InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [n23K5InvFor] using n23K5DecodeInv01
  case «1» => simpa [n23K5InvFor] using n23K5DecodeInv02
  case «2» => simpa [n23K5InvFor] using n23K5DecodeInv03
  case «3» => simpa [n23K5InvFor] using n23K5DecodeInv04
  case «4» => simpa [n23K5InvFor] using n23K5DecodeInv05
  case «5» => simpa [n23K5InvFor] using n23K5DecodeInv06
  case «6» => simpa [n23K5InvFor] using n23K5DecodeInv07
  case «7» => simpa [n23K5InvFor] using n23K5DecodeInv08
  case «8» => simpa [n23K5InvFor] using n23K5DecodeInv09
  case «9» => simpa [n23K5InvFor] using n23K5DecodeInv10
  case «10» => simpa [n23K5InvFor] using n23K5DecodeInv11
  case «11» => simpa [n23K5InvFor] using n23K5DecodeInv12
  case «12» => simpa [n23K5InvFor] using n23K5DecodeInv13
  case «13» => simpa [n23K5InvFor] using n23K5DecodeInv14
  case «14» => simpa [n23K5InvFor] using n23K5DecodeInv15
  case «15» => simpa [n23K5InvFor] using n23K5DecodeInv16
  case «16» => simpa [n23K5InvFor] using n23K5DecodeInv17
  case «17» => simpa [n23K5InvFor] using n23K5DecodeInv18
  case «18» => simpa [n23K5InvFor] using n23K5DecodeInv19
  case «19» => simpa [n23K5InvFor] using n23K5DecodeInv20
  case «20» => simpa [n23K5InvFor] using n23K5DecodeInv21
  case «21» => simpa [n23K5InvFor] using n23K5DecodeInv22
  case «22» => simpa [n23K5InvFor] using n23K5DecodeInv23
  case «23» => simpa [n23K5InvFor] using n23K5DecodeInv24
  case «24» => simpa [n23K5InvFor] using n23K5DecodeInv25
  case «25» => simpa [n23K5InvFor] using n23K5DecodeInv26
  case «26» => simpa [n23K5InvFor] using n23K5DecodeInv27
  case «27» => simpa [n23K5InvFor] using n23K5DecodeInv28
  case «28» => simpa [n23K5InvFor] using n23K5DecodeInv29
  case «29» => simpa [n23K5InvFor] using n23K5DecodeInv30
  case «30» => simpa [n23K5InvFor] using n23K5DecodeInv31
theorem n23K5InvFor_sum_zero : (∑ i : Fin 31, n23K5InvFor i) = 0 := by
  have h := n23K5InverseSumAdjoin
  simp [Fin.sum_univ_succ, n23K5InvFor]
  convert h using 1 <;> ring
#print axioms n23K5DecodeInvSucc
#print axioms n23K5InvFor_sum_zero


