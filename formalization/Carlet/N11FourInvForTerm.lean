import Carlet.N11FourDecodeInverseProbe
import Carlet.N11FourInverseAdjoinProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

def e11InvFor (i : Fin 15) : AdjoinRoot f := AdjoinRoot.mk f (match i.val with
  | 0 => e11I01
  | 1 => e11I02
  | 2 => e11I03
  | 3 => e11I04
  | 4 => e11I05
  | 5 => e11I06
  | 6 => e11I07
  | 7 => e11I08
  | 8 => e11I09
  | 9 => e11I10
  | 10 => e11I11
  | 11 => e11I12
  | 12 => e11I13
  | 13 => e11I14
  | 14 => e11I15
  | _ => 0)

theorem e11DecodeInvSucc (i : Fin 15) : (e11SubsetSum (subsetDecode11Four i.succ))⁻¹ = e11InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [e11InvFor] using e11DecodeInv01
  case «1» => simpa [e11InvFor] using e11DecodeInv02
  case «2» => simpa [e11InvFor] using e11DecodeInv03
  case «3» => simpa [e11InvFor] using e11DecodeInv04
  case «4» => simpa [e11InvFor] using e11DecodeInv05
  case «5» => simpa [e11InvFor] using e11DecodeInv06
  case «6» => simpa [e11InvFor] using e11DecodeInv07
  case «7» => simpa [e11InvFor] using e11DecodeInv08
  case «8» => simpa [e11InvFor] using e11DecodeInv09
  case «9» => simpa [e11InvFor] using e11DecodeInv10
  case «10» => simpa [e11InvFor] using e11DecodeInv11
  case «11» => simpa [e11InvFor] using e11DecodeInv12
  case «12» => simpa [e11InvFor] using e11DecodeInv13
  case «13» => simpa [e11InvFor] using e11DecodeInv14
  case «14» => simpa [e11InvFor] using e11DecodeInv15

#print axioms e11DecodeInvSucc


theorem e11InvFor_sum_zero : (∑ i : Fin 15, e11InvFor i) = 0 := by
  have h := e11InverseSumAdjoin
  simp [Fin.sum_univ_succ, e11InvFor]
  convert h using 1; ring
#print axioms e11InvFor_sum_zero
