import Carlet.N11DecodeInverseAudit
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩

def certInvFor (i : Fin 31) : AdjoinRoot f := AdjoinRoot.mk f (match i.val with
  | 0 => certI01
  | 1 => certI02
  | 2 => certI03
  | 3 => certI04
  | 4 => certI05
  | 5 => certI06
  | 6 => certI07
  | 7 => certI08
  | 8 => certI09
  | 9 => certI10
  | 10 => certI11
  | 11 => certI12
  | 12 => certI13
  | 13 => certI14
  | 14 => certI15
  | 15 => certI16
  | 16 => certI17
  | 17 => certI18
  | 18 => certI19
  | 19 => certI20
  | 20 => certI21
  | 21 => certI22
  | 22 => certI23
  | 23 => certI24
  | 24 => certI25
  | 25 => certI26
  | 26 => certI27
  | 27 => certI28
  | 28 => certI29
  | 29 => certI30
  | 30 => certI31
  | _ => 0)

theorem certDecodeInvSucc (i : Fin 31) : (certSubsetSum (subsetDecode i.succ))⁻¹ = certInvFor i := by
  classical
  fin_cases i
  case «0» => simpa [certInvFor] using certDecodeInv01_fast
  case «1» => simpa [certInvFor] using certDecodeInv02
  case «2» => simpa [certInvFor] using certDecodeInv03
  case «3» => simpa [certInvFor] using certDecodeInv04
  case «4» => simpa [certInvFor] using certDecodeInv05
  case «5» => simpa [certInvFor] using certDecodeInv06
  case «6» => simpa [certInvFor] using certDecodeInv07
  case «7» => simpa [certInvFor] using certDecodeInv08
  case «8» => simpa [certInvFor] using certDecodeInv09
  case «9» => simpa [certInvFor] using certDecodeInv10
  case «10» => simpa [certInvFor] using certDecodeInv11
  case «11» => simpa [certInvFor] using certDecodeInv12
  case «12» => simpa [certInvFor] using certDecodeInv13
  case «13» => simpa [certInvFor] using certDecodeInv14
  case «14» => simpa [certInvFor] using certDecodeInv15
  case «15» => simpa [certInvFor] using certDecodeInv16
  case «16» => simpa [certInvFor] using certDecodeInv17
  case «17» => simpa [certInvFor] using certDecodeInv18
  case «18» => simpa [certInvFor] using certDecodeInv19
  case «19» => simpa [certInvFor] using certDecodeInv20
  case «20» => simpa [certInvFor] using certDecodeInv21
  case «21» => simpa [certInvFor] using certDecodeInv22
  case «22» => simpa [certInvFor] using certDecodeInv23
  case «23» => simpa [certInvFor] using certDecodeInv24
  case «24» => simpa [certInvFor] using certDecodeInv25
  case «25» => simpa [certInvFor] using certDecodeInv26
  case «26» => simpa [certInvFor] using certDecodeInv27
  case «27» => simpa [certInvFor] using certDecodeInv28
  case «28» => simpa [certInvFor] using certDecodeInv29
  case «29» => simpa [certInvFor] using certDecodeInv30
  case «30» => simpa [certInvFor] using certDecodeInv31

#print axioms certDecodeInvSucc

theorem certInvBlock01to08 :
    (∑ i : Fin 8, certInvFor (Fin.castAdd 23 i)) =
      AdjoinRoot.mk f certI01 + AdjoinRoot.mk f certI02 + AdjoinRoot.mk f certI03 + AdjoinRoot.mk f certI04 +
      AdjoinRoot.mk f certI05 + AdjoinRoot.mk f certI06 + AdjoinRoot.mk f certI07 + AdjoinRoot.mk f certI08 := by
  simp [Fin.sum_univ_succ, certInvFor, Fin.val_castAdd]
  ring

theorem certInvBlock09to16 :
    (∑ i : Fin 8, certInvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) =
      AdjoinRoot.mk f certI09 + AdjoinRoot.mk f certI10 + AdjoinRoot.mk f certI11 + AdjoinRoot.mk f certI12 +
      AdjoinRoot.mk f certI13 + AdjoinRoot.mk f certI14 + AdjoinRoot.mk f certI15 + AdjoinRoot.mk f certI16 := by
  simp [Fin.sum_univ_succ, certInvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem certInvBlock17to24 :
    (∑ i : Fin 8, certInvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) =
      AdjoinRoot.mk f certI17 + AdjoinRoot.mk f certI18 + AdjoinRoot.mk f certI19 + AdjoinRoot.mk f certI20 +
      AdjoinRoot.mk f certI21 + AdjoinRoot.mk f certI22 + AdjoinRoot.mk f certI23 + AdjoinRoot.mk f certI24 := by
  simp [Fin.sum_univ_succ, certInvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem certInvBlock25to31 :
    (∑ i : Fin 7, certInvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i)))) =
      AdjoinRoot.mk f certI25 + AdjoinRoot.mk f certI26 + AdjoinRoot.mk f certI27 + AdjoinRoot.mk f certI28 +
      AdjoinRoot.mk f certI29 + AdjoinRoot.mk f certI30 + AdjoinRoot.mk f certI31 := by
  simp [Fin.sum_univ_succ, certInvFor, Fin.val_natAdd]
  ring

theorem certInvFor_sum_zero : (∑ i : Fin 31, certInvFor i) = 0 := by
  calc
    (∑ i : Fin 31, certInvFor i) =
        (∑ i : Fin 8, certInvFor (Fin.castAdd 23 i)) + (∑ j : Fin 23, certInvFor (Fin.natAdd 8 j)) := by
      exact Fin.sum_univ_add (a := 8) (b := 23) (f := certInvFor)
    _ = (∑ i : Fin 8, certInvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, certInvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         (∑ j : Fin 15, certInvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 15)
        (f := fun j : Fin 23 => certInvFor (Fin.natAdd 8 j))
      simpa using hsplit
    _ = (∑ i : Fin 8, certInvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, certInvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         ((∑ i : Fin 8, certInvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) +
          (∑ j : Fin 7, certInvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 j)))))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 7)
        (f := fun j : Fin 15 => certInvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))
      simpa using hsplit
    _ = 0 := by
      rw [certInvBlock01to08]
      rw [certInvBlock09to16]
      rw [certInvBlock17to24]
      rw [certInvBlock25to31]
      rw [← cert_inverse_sum_adjoin]
      abel
#print axioms certInvFor_sum_zero


