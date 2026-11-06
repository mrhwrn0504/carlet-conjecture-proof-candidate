import Carlet.N19FourDecodeInverseProbe
import Carlet.N19FourInverseAdjoinProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩

def e19InvFor (i : Fin 15) : AdjoinRoot f19 := AdjoinRoot.mk f19 (match i.val with
  | 0 => e19I01
  | 1 => e19I02
  | 2 => e19I03
  | 3 => e19I04
  | 4 => e19I05
  | 5 => e19I06
  | 6 => e19I07
  | 7 => e19I08
  | 8 => e19I09
  | 9 => e19I10
  | 10 => e19I11
  | 11 => e19I12
  | 12 => e19I13
  | 13 => e19I14
  | 14 => e19I15
  | _ => 0)

theorem e19DecodeInvSucc (i : Fin 15) : (e19SubsetSum (subsetDecode19Four i.succ))⁻¹ = e19InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [e19InvFor] using e19DecodeInv01
  case «1» => simpa [e19InvFor] using e19DecodeInv02
  case «2» => simpa [e19InvFor] using e19DecodeInv03
  case «3» => simpa [e19InvFor] using e19DecodeInv04
  case «4» => simpa [e19InvFor] using e19DecodeInv05
  case «5» => simpa [e19InvFor] using e19DecodeInv06
  case «6» => simpa [e19InvFor] using e19DecodeInv07
  case «7» => simpa [e19InvFor] using e19DecodeInv08
  case «8» => simpa [e19InvFor] using e19DecodeInv09
  case «9» => simpa [e19InvFor] using e19DecodeInv10
  case «10» => simpa [e19InvFor] using e19DecodeInv11
  case «11» => simpa [e19InvFor] using e19DecodeInv12
  case «12» => simpa [e19InvFor] using e19DecodeInv13
  case «13» => simpa [e19InvFor] using e19DecodeInv14
  case «14» => simpa [e19InvFor] using e19DecodeInv15

#print axioms e19DecodeInvSucc


theorem e19InvFor_sum_zero : (∑ i : Fin 15, e19InvFor i) = 0 := by
  have h := e19InverseSumAdjoin
  simp [Fin.sum_univ_succ, e19InvFor]
  convert h using 1; ring
#print axioms e19InvFor_sum_zero
