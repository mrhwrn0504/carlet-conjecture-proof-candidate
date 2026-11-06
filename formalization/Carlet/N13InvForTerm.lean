import Carlet.N13DecodeInverseProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩

def cert13InvFor (i : Fin 31) : AdjoinRoot f13 := AdjoinRoot.mk f13 (match i.val with
  | 0 => cert13I01
  | 1 => cert13I02
  | 2 => cert13I03
  | 3 => cert13I04
  | 4 => cert13I05
  | 5 => cert13I06
  | 6 => cert13I07
  | 7 => cert13I08
  | 8 => cert13I09
  | 9 => cert13I10
  | 10 => cert13I11
  | 11 => cert13I12
  | 12 => cert13I13
  | 13 => cert13I14
  | 14 => cert13I15
  | 15 => cert13I16
  | 16 => cert13I17
  | 17 => cert13I18
  | 18 => cert13I19
  | 19 => cert13I20
  | 20 => cert13I21
  | 21 => cert13I22
  | 22 => cert13I23
  | 23 => cert13I24
  | 24 => cert13I25
  | 25 => cert13I26
  | 26 => cert13I27
  | 27 => cert13I28
  | 28 => cert13I29
  | 29 => cert13I30
  | 30 => cert13I31
  | _ => 0)

theorem cert13DecodeInvSucc (i : Fin 31) : (cert13SubsetSum (subsetDecode13 i.succ))⁻¹ = cert13InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [cert13InvFor] using cert13DecodeInv01
  case «1» => simpa [cert13InvFor] using cert13DecodeInv02
  case «2» => simpa [cert13InvFor] using cert13DecodeInv03
  case «3» => simpa [cert13InvFor] using cert13DecodeInv04
  case «4» => simpa [cert13InvFor] using cert13DecodeInv05
  case «5» => simpa [cert13InvFor] using cert13DecodeInv06
  case «6» => simpa [cert13InvFor] using cert13DecodeInv07
  case «7» => simpa [cert13InvFor] using cert13DecodeInv08
  case «8» => simpa [cert13InvFor] using cert13DecodeInv09
  case «9» => simpa [cert13InvFor] using cert13DecodeInv10
  case «10» => simpa [cert13InvFor] using cert13DecodeInv11
  case «11» => simpa [cert13InvFor] using cert13DecodeInv12
  case «12» => simpa [cert13InvFor] using cert13DecodeInv13
  case «13» => simpa [cert13InvFor] using cert13DecodeInv14
  case «14» => simpa [cert13InvFor] using cert13DecodeInv15
  case «15» => simpa [cert13InvFor] using cert13DecodeInv16
  case «16» => simpa [cert13InvFor] using cert13DecodeInv17
  case «17» => simpa [cert13InvFor] using cert13DecodeInv18
  case «18» => simpa [cert13InvFor] using cert13DecodeInv19
  case «19» => simpa [cert13InvFor] using cert13DecodeInv20
  case «20» => simpa [cert13InvFor] using cert13DecodeInv21
  case «21» => simpa [cert13InvFor] using cert13DecodeInv22
  case «22» => simpa [cert13InvFor] using cert13DecodeInv23
  case «23» => simpa [cert13InvFor] using cert13DecodeInv24
  case «24» => simpa [cert13InvFor] using cert13DecodeInv25
  case «25» => simpa [cert13InvFor] using cert13DecodeInv26
  case «26» => simpa [cert13InvFor] using cert13DecodeInv27
  case «27» => simpa [cert13InvFor] using cert13DecodeInv28
  case «28» => simpa [cert13InvFor] using cert13DecodeInv29
  case «29» => simpa [cert13InvFor] using cert13DecodeInv30
  case «30» => simpa [cert13InvFor] using cert13DecodeInv31

#print axioms cert13DecodeInvSucc

theorem cert13InvBlock01to08 :
    (∑ i : Fin 8, cert13InvFor (Fin.castAdd 23 i)) =
      AdjoinRoot.mk f13 cert13I01 + AdjoinRoot.mk f13 cert13I02 + AdjoinRoot.mk f13 cert13I03 + AdjoinRoot.mk f13 cert13I04 +
      AdjoinRoot.mk f13 cert13I05 + AdjoinRoot.mk f13 cert13I06 + AdjoinRoot.mk f13 cert13I07 + AdjoinRoot.mk f13 cert13I08 := by
  simp [Fin.sum_univ_succ, cert13InvFor, Fin.val_castAdd]
  ring

theorem cert13InvBlock09to16 :
    (∑ i : Fin 8, cert13InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) =
      AdjoinRoot.mk f13 cert13I09 + AdjoinRoot.mk f13 cert13I10 + AdjoinRoot.mk f13 cert13I11 + AdjoinRoot.mk f13 cert13I12 +
      AdjoinRoot.mk f13 cert13I13 + AdjoinRoot.mk f13 cert13I14 + AdjoinRoot.mk f13 cert13I15 + AdjoinRoot.mk f13 cert13I16 := by
  simp [Fin.sum_univ_succ, cert13InvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem cert13InvBlock17to24 :
    (∑ i : Fin 8, cert13InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) =
      AdjoinRoot.mk f13 cert13I17 + AdjoinRoot.mk f13 cert13I18 + AdjoinRoot.mk f13 cert13I19 + AdjoinRoot.mk f13 cert13I20 +
      AdjoinRoot.mk f13 cert13I21 + AdjoinRoot.mk f13 cert13I22 + AdjoinRoot.mk f13 cert13I23 + AdjoinRoot.mk f13 cert13I24 := by
  simp [Fin.sum_univ_succ, cert13InvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem cert13InvBlock25to31 :
    (∑ i : Fin 7, cert13InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i)))) =
      AdjoinRoot.mk f13 cert13I25 + AdjoinRoot.mk f13 cert13I26 + AdjoinRoot.mk f13 cert13I27 + AdjoinRoot.mk f13 cert13I28 +
      AdjoinRoot.mk f13 cert13I29 + AdjoinRoot.mk f13 cert13I30 + AdjoinRoot.mk f13 cert13I31 := by
  simp [Fin.sum_univ_succ, cert13InvFor, Fin.val_natAdd]
  ring

theorem cert13InvFor_sum_zero : (∑ i : Fin 31, cert13InvFor i) = 0 := by
  calc
    (∑ i : Fin 31, cert13InvFor i) =
        (∑ i : Fin 8, cert13InvFor (Fin.castAdd 23 i)) + (∑ j : Fin 23, cert13InvFor (Fin.natAdd 8 j)) := by
      exact Fin.sum_univ_add (a := 8) (b := 23) (f := cert13InvFor)
    _ = (∑ i : Fin 8, cert13InvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, cert13InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         (∑ j : Fin 15, cert13InvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 15)
        (f := fun j : Fin 23 => cert13InvFor (Fin.natAdd 8 j))
      simpa using hsplit
    _ = (∑ i : Fin 8, cert13InvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, cert13InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         ((∑ i : Fin 8, cert13InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) +
          (∑ j : Fin 7, cert13InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 j)))))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 7)
        (f := fun j : Fin 15 => cert13InvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))
      simpa using hsplit
    _ = 0 := by
      rw [cert13InvBlock01to08]
      rw [cert13InvBlock09to16]
      rw [cert13InvBlock17to24]
      rw [cert13InvBlock25to31]
      rw [← cert13_inverse_sum_adjoin]
      abel
#print axioms cert13InvFor_sum_zero



