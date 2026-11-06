import Carlet.N29K5DecodeInverseProbe
import Carlet.N29K5InverseAdjoinProbe
import Mathlib.Tactic
open Carlet
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f29K5) := ⟨f29K5_irreducible⟩
def n29K5InvFor (i : Fin 31) : AdjoinRoot f29K5 := AdjoinRoot.mk f29K5 (match i.val with
  | 0 => n29K5I01
  | 1 => n29K5I02
  | 2 => n29K5I03
  | 3 => n29K5I04
  | 4 => n29K5I05
  | 5 => n29K5I06
  | 6 => n29K5I07
  | 7 => n29K5I08
  | 8 => n29K5I09
  | 9 => n29K5I10
  | 10 => n29K5I11
  | 11 => n29K5I12
  | 12 => n29K5I13
  | 13 => n29K5I14
  | 14 => n29K5I15
  | 15 => n29K5I16
  | 16 => n29K5I17
  | 17 => n29K5I18
  | 18 => n29K5I19
  | 19 => n29K5I20
  | 20 => n29K5I21
  | 21 => n29K5I22
  | 22 => n29K5I23
  | 23 => n29K5I24
  | 24 => n29K5I25
  | 25 => n29K5I26
  | 26 => n29K5I27
  | 27 => n29K5I28
  | 28 => n29K5I29
  | 29 => n29K5I30
  | 30 => n29K5I31
  | _ => 0)
theorem n29K5DecodeInvSucc (i : Fin 31) : (n29K5SubsetSum (n29K5SubsetDecode i.succ))⁻¹ = n29K5InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [n29K5InvFor] using n29K5DecodeInv01
  case «1» => simpa [n29K5InvFor] using n29K5DecodeInv02
  case «2» => simpa [n29K5InvFor] using n29K5DecodeInv03
  case «3» => simpa [n29K5InvFor] using n29K5DecodeInv04
  case «4» => simpa [n29K5InvFor] using n29K5DecodeInv05
  case «5» => simpa [n29K5InvFor] using n29K5DecodeInv06
  case «6» => simpa [n29K5InvFor] using n29K5DecodeInv07
  case «7» => simpa [n29K5InvFor] using n29K5DecodeInv08
  case «8» => simpa [n29K5InvFor] using n29K5DecodeInv09
  case «9» => simpa [n29K5InvFor] using n29K5DecodeInv10
  case «10» => simpa [n29K5InvFor] using n29K5DecodeInv11
  case «11» => simpa [n29K5InvFor] using n29K5DecodeInv12
  case «12» => simpa [n29K5InvFor] using n29K5DecodeInv13
  case «13» => simpa [n29K5InvFor] using n29K5DecodeInv14
  case «14» => simpa [n29K5InvFor] using n29K5DecodeInv15
  case «15» => simpa [n29K5InvFor] using n29K5DecodeInv16
  case «16» => simpa [n29K5InvFor] using n29K5DecodeInv17
  case «17» => simpa [n29K5InvFor] using n29K5DecodeInv18
  case «18» => simpa [n29K5InvFor] using n29K5DecodeInv19
  case «19» => simpa [n29K5InvFor] using n29K5DecodeInv20
  case «20» => simpa [n29K5InvFor] using n29K5DecodeInv21
  case «21» => simpa [n29K5InvFor] using n29K5DecodeInv22
  case «22» => simpa [n29K5InvFor] using n29K5DecodeInv23
  case «23» => simpa [n29K5InvFor] using n29K5DecodeInv24
  case «24» => simpa [n29K5InvFor] using n29K5DecodeInv25
  case «25» => simpa [n29K5InvFor] using n29K5DecodeInv26
  case «26» => simpa [n29K5InvFor] using n29K5DecodeInv27
  case «27» => simpa [n29K5InvFor] using n29K5DecodeInv28
  case «28» => simpa [n29K5InvFor] using n29K5DecodeInv29
  case «29» => simpa [n29K5InvFor] using n29K5DecodeInv30
  case «30» => simpa [n29K5InvFor] using n29K5DecodeInv31
theorem n29K5InvFor_sum_zero : (∑ i : Fin 31, n29K5InvFor i) = 0 := by
  have h := n29K5InverseSumAdjoin
  simp [Fin.sum_univ_succ, n29K5InvFor]
  convert h using 1 <;> ring
#print axioms n29K5DecodeInvSucc
#print axioms n29K5InvFor_sum_zero


