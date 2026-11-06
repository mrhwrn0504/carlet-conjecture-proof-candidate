import Carlet.N17FourDecodeInverseProbe
import Carlet.N17FourInverseAdjoinProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩

def e17InvFor (i : Fin 15) : AdjoinRoot f17 := AdjoinRoot.mk f17 (match i.val with
  | 0 => e17I01
  | 1 => e17I02
  | 2 => e17I03
  | 3 => e17I04
  | 4 => e17I05
  | 5 => e17I06
  | 6 => e17I07
  | 7 => e17I08
  | 8 => e17I09
  | 9 => e17I10
  | 10 => e17I11
  | 11 => e17I12
  | 12 => e17I13
  | 13 => e17I14
  | 14 => e17I15
  | _ => 0)

theorem e17DecodeInvSucc (i : Fin 15) : (e17SubsetSum (subsetDecode17Four i.succ))⁻¹ = e17InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [e17InvFor] using e17DecodeInv01
  case «1» => simpa [e17InvFor] using e17DecodeInv02
  case «2» => simpa [e17InvFor] using e17DecodeInv03
  case «3» => simpa [e17InvFor] using e17DecodeInv04
  case «4» => simpa [e17InvFor] using e17DecodeInv05
  case «5» => simpa [e17InvFor] using e17DecodeInv06
  case «6» => simpa [e17InvFor] using e17DecodeInv07
  case «7» => simpa [e17InvFor] using e17DecodeInv08
  case «8» => simpa [e17InvFor] using e17DecodeInv09
  case «9» => simpa [e17InvFor] using e17DecodeInv10
  case «10» => simpa [e17InvFor] using e17DecodeInv11
  case «11» => simpa [e17InvFor] using e17DecodeInv12
  case «12» => simpa [e17InvFor] using e17DecodeInv13
  case «13» => simpa [e17InvFor] using e17DecodeInv14
  case «14» => simpa [e17InvFor] using e17DecodeInv15

#print axioms e17DecodeInvSucc


theorem e17InvFor_sum_zero : (∑ i : Fin 15, e17InvFor i) = 0 := by
  have h := e17InverseSumAdjoin
  simp [Fin.sum_univ_succ, e17InvFor]
  convert h using 1; ring
#print axioms e17InvFor_sum_zero
