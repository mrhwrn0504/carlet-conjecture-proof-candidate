import Carlet.N9DecodeInverseProbe
import Carlet.N9InverseAdjoinProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩

def d9InvFor (i : Fin 15) : AdjoinRoot f9 := AdjoinRoot.mk f9 (match i.val with
  | 0 => d9I01
  | 1 => d9I02
  | 2 => d9I03
  | 3 => d9I04
  | 4 => d9I05
  | 5 => d9I06
  | 6 => d9I07
  | 7 => d9I08
  | 8 => d9I09
  | 9 => d9I10
  | 10 => d9I11
  | 11 => d9I12
  | 12 => d9I13
  | 13 => d9I14
  | 14 => d9I15
  | _ => 0)

theorem d9DecodeInvSucc (i : Fin 15) : (d9SubsetSum (subsetDecode9 i.succ))⁻¹ = d9InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [d9InvFor] using d9DecodeInv01
  case «1» => simpa [d9InvFor] using d9DecodeInv02
  case «2» => simpa [d9InvFor] using d9DecodeInv03
  case «3» => simpa [d9InvFor] using d9DecodeInv04
  case «4» => simpa [d9InvFor] using d9DecodeInv05
  case «5» => simpa [d9InvFor] using d9DecodeInv06
  case «6» => simpa [d9InvFor] using d9DecodeInv07
  case «7» => simpa [d9InvFor] using d9DecodeInv08
  case «8» => simpa [d9InvFor] using d9DecodeInv09
  case «9» => simpa [d9InvFor] using d9DecodeInv10
  case «10» => simpa [d9InvFor] using d9DecodeInv11
  case «11» => simpa [d9InvFor] using d9DecodeInv12
  case «12» => simpa [d9InvFor] using d9DecodeInv13
  case «13» => simpa [d9InvFor] using d9DecodeInv14
  case «14» => simpa [d9InvFor] using d9DecodeInv15

#print axioms d9DecodeInvSucc


theorem d9InvFor_sum_zero : (∑ i : Fin 15, d9InvFor i) = 0 := by
  have h := d9InverseSumAdjoin
  simp [Fin.sum_univ_succ, d9InvFor]
  convert h using 1; ring
#print axioms d9InvFor_sum_zero
