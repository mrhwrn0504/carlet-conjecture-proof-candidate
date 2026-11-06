import Carlet.N9K5DecodeInverseProbe
import Carlet.N9K5InverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
def n9K5InvFor (i : Fin 31) : AdjoinRoot f9 := AdjoinRoot.mk f9 (match i.val with
  | 0 => n9K5I01
  | 1 => n9K5I02
  | 2 => n9K5I03
  | 3 => n9K5I04
  | 4 => n9K5I05
  | 5 => n9K5I06
  | 6 => n9K5I07
  | 7 => n9K5I08
  | 8 => n9K5I09
  | 9 => n9K5I10
  | 10 => n9K5I11
  | 11 => n9K5I12
  | 12 => n9K5I13
  | 13 => n9K5I14
  | 14 => n9K5I15
  | 15 => n9K5I16
  | 16 => n9K5I17
  | 17 => n9K5I18
  | 18 => n9K5I19
  | 19 => n9K5I20
  | 20 => n9K5I21
  | 21 => n9K5I22
  | 22 => n9K5I23
  | 23 => n9K5I24
  | 24 => n9K5I25
  | 25 => n9K5I26
  | 26 => n9K5I27
  | 27 => n9K5I28
  | 28 => n9K5I29
  | 29 => n9K5I30
  | 30 => n9K5I31
  | _ => 0)
theorem n9K5DecodeInvSucc (i : Fin 31) : (n9K5SubsetSum (n9K5SubsetDecode i.succ))⁻¹ = n9K5InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [n9K5InvFor] using n9K5DecodeInv01
  case «1» => simpa [n9K5InvFor] using n9K5DecodeInv02
  case «2» => simpa [n9K5InvFor] using n9K5DecodeInv03
  case «3» => simpa [n9K5InvFor] using n9K5DecodeInv04
  case «4» => simpa [n9K5InvFor] using n9K5DecodeInv05
  case «5» => simpa [n9K5InvFor] using n9K5DecodeInv06
  case «6» => simpa [n9K5InvFor] using n9K5DecodeInv07
  case «7» => simpa [n9K5InvFor] using n9K5DecodeInv08
  case «8» => simpa [n9K5InvFor] using n9K5DecodeInv09
  case «9» => simpa [n9K5InvFor] using n9K5DecodeInv10
  case «10» => simpa [n9K5InvFor] using n9K5DecodeInv11
  case «11» => simpa [n9K5InvFor] using n9K5DecodeInv12
  case «12» => simpa [n9K5InvFor] using n9K5DecodeInv13
  case «13» => simpa [n9K5InvFor] using n9K5DecodeInv14
  case «14» => simpa [n9K5InvFor] using n9K5DecodeInv15
  case «15» => simpa [n9K5InvFor] using n9K5DecodeInv16
  case «16» => simpa [n9K5InvFor] using n9K5DecodeInv17
  case «17» => simpa [n9K5InvFor] using n9K5DecodeInv18
  case «18» => simpa [n9K5InvFor] using n9K5DecodeInv19
  case «19» => simpa [n9K5InvFor] using n9K5DecodeInv20
  case «20» => simpa [n9K5InvFor] using n9K5DecodeInv21
  case «21» => simpa [n9K5InvFor] using n9K5DecodeInv22
  case «22» => simpa [n9K5InvFor] using n9K5DecodeInv23
  case «23» => simpa [n9K5InvFor] using n9K5DecodeInv24
  case «24» => simpa [n9K5InvFor] using n9K5DecodeInv25
  case «25» => simpa [n9K5InvFor] using n9K5DecodeInv26
  case «26» => simpa [n9K5InvFor] using n9K5DecodeInv27
  case «27» => simpa [n9K5InvFor] using n9K5DecodeInv28
  case «28» => simpa [n9K5InvFor] using n9K5DecodeInv29
  case «29» => simpa [n9K5InvFor] using n9K5DecodeInv30
  case «30» => simpa [n9K5InvFor] using n9K5DecodeInv31
theorem n9K5InvFor_sum_zero : (∑ i : Fin 31, n9K5InvFor i) = 0 := by
  have h := n9K5InverseSumAdjoin
  simp [Fin.sum_univ_succ, n9K5InvFor]
  convert h using 1 <;> ring
#print axioms n9K5DecodeInvSucc
#print axioms n9K5InvFor_sum_zero


