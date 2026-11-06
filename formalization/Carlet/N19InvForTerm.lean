import Carlet.N19DecodeInverseProbe
import Carlet.N19InverseAdjoinProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩

def c19InvFor (i : Fin 31) : AdjoinRoot f19 := AdjoinRoot.mk f19 (match i.val with
  | 0 => c19I01
  | 1 => c19I02
  | 2 => c19I03
  | 3 => c19I04
  | 4 => c19I05
  | 5 => c19I06
  | 6 => c19I07
  | 7 => c19I08
  | 8 => c19I09
  | 9 => c19I10
  | 10 => c19I11
  | 11 => c19I12
  | 12 => c19I13
  | 13 => c19I14
  | 14 => c19I15
  | 15 => c19I16
  | 16 => c19I17
  | 17 => c19I18
  | 18 => c19I19
  | 19 => c19I20
  | 20 => c19I21
  | 21 => c19I22
  | 22 => c19I23
  | 23 => c19I24
  | 24 => c19I25
  | 25 => c19I26
  | 26 => c19I27
  | 27 => c19I28
  | 28 => c19I29
  | 29 => c19I30
  | 30 => c19I31
  | _ => 0)

theorem c19DecodeInvSucc (i : Fin 31) : (c19SubsetSum (subsetDecode19 i.succ))⁻¹ = c19InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [c19InvFor] using c19DecodeInv01
  case «1» => simpa [c19InvFor] using c19DecodeInv02
  case «2» => simpa [c19InvFor] using c19DecodeInv03
  case «3» => simpa [c19InvFor] using c19DecodeInv04
  case «4» => simpa [c19InvFor] using c19DecodeInv05
  case «5» => simpa [c19InvFor] using c19DecodeInv06
  case «6» => simpa [c19InvFor] using c19DecodeInv07
  case «7» => simpa [c19InvFor] using c19DecodeInv08
  case «8» => simpa [c19InvFor] using c19DecodeInv09
  case «9» => simpa [c19InvFor] using c19DecodeInv10
  case «10» => simpa [c19InvFor] using c19DecodeInv11
  case «11» => simpa [c19InvFor] using c19DecodeInv12
  case «12» => simpa [c19InvFor] using c19DecodeInv13
  case «13» => simpa [c19InvFor] using c19DecodeInv14
  case «14» => simpa [c19InvFor] using c19DecodeInv15
  case «15» => simpa [c19InvFor] using c19DecodeInv16
  case «16» => simpa [c19InvFor] using c19DecodeInv17
  case «17» => simpa [c19InvFor] using c19DecodeInv18
  case «18» => simpa [c19InvFor] using c19DecodeInv19
  case «19» => simpa [c19InvFor] using c19DecodeInv20
  case «20» => simpa [c19InvFor] using c19DecodeInv21
  case «21» => simpa [c19InvFor] using c19DecodeInv22
  case «22» => simpa [c19InvFor] using c19DecodeInv23
  case «23» => simpa [c19InvFor] using c19DecodeInv24
  case «24» => simpa [c19InvFor] using c19DecodeInv25
  case «25» => simpa [c19InvFor] using c19DecodeInv26
  case «26» => simpa [c19InvFor] using c19DecodeInv27
  case «27» => simpa [c19InvFor] using c19DecodeInv28
  case «28» => simpa [c19InvFor] using c19DecodeInv29
  case «29» => simpa [c19InvFor] using c19DecodeInv30
  case «30» => simpa [c19InvFor] using c19DecodeInv31

#print axioms c19DecodeInvSucc

theorem c19InvBlock01to08 :
    (∑ i : Fin 8, c19InvFor (Fin.castAdd 23 i)) =
      AdjoinRoot.mk f19 c19I01 + AdjoinRoot.mk f19 c19I02 + AdjoinRoot.mk f19 c19I03 + AdjoinRoot.mk f19 c19I04 +
      AdjoinRoot.mk f19 c19I05 + AdjoinRoot.mk f19 c19I06 + AdjoinRoot.mk f19 c19I07 + AdjoinRoot.mk f19 c19I08 := by
  simp [Fin.sum_univ_succ, c19InvFor, Fin.val_castAdd]
  ring

theorem c19InvBlock09to16 :
    (∑ i : Fin 8, c19InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) =
      AdjoinRoot.mk f19 c19I09 + AdjoinRoot.mk f19 c19I10 + AdjoinRoot.mk f19 c19I11 + AdjoinRoot.mk f19 c19I12 +
      AdjoinRoot.mk f19 c19I13 + AdjoinRoot.mk f19 c19I14 + AdjoinRoot.mk f19 c19I15 + AdjoinRoot.mk f19 c19I16 := by
  simp [Fin.sum_univ_succ, c19InvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem c19InvBlock17to24 :
    (∑ i : Fin 8, c19InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) =
      AdjoinRoot.mk f19 c19I17 + AdjoinRoot.mk f19 c19I18 + AdjoinRoot.mk f19 c19I19 + AdjoinRoot.mk f19 c19I20 +
      AdjoinRoot.mk f19 c19I21 + AdjoinRoot.mk f19 c19I22 + AdjoinRoot.mk f19 c19I23 + AdjoinRoot.mk f19 c19I24 := by
  simp [Fin.sum_univ_succ, c19InvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem c19InvBlock25to31 :
    (∑ i : Fin 7, c19InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i)))) =
      AdjoinRoot.mk f19 c19I25 + AdjoinRoot.mk f19 c19I26 + AdjoinRoot.mk f19 c19I27 + AdjoinRoot.mk f19 c19I28 +
      AdjoinRoot.mk f19 c19I29 + AdjoinRoot.mk f19 c19I30 + AdjoinRoot.mk f19 c19I31 := by
  simp [Fin.sum_univ_succ, c19InvFor, Fin.val_natAdd]
  ring

theorem c19InvFor_sum_zero : (∑ i : Fin 31, c19InvFor i) = 0 := by
  calc
    (∑ i : Fin 31, c19InvFor i) =
        (∑ i : Fin 8, c19InvFor (Fin.castAdd 23 i)) + (∑ j : Fin 23, c19InvFor (Fin.natAdd 8 j)) := by
      exact Fin.sum_univ_add (a := 8) (b := 23) (f := c19InvFor)
    _ = (∑ i : Fin 8, c19InvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, c19InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         (∑ j : Fin 15, c19InvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 15)
        (f := fun j : Fin 23 => c19InvFor (Fin.natAdd 8 j))
      simpa using hsplit
    _ = (∑ i : Fin 8, c19InvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, c19InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         ((∑ i : Fin 8, c19InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) +
          (∑ j : Fin 7, c19InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 j)))))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 7)
        (f := fun j : Fin 15 => c19InvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))
      simpa using hsplit
    _ = 0 := by
      rw [c19InvBlock01to08]
      rw [c19InvBlock09to16]
      rw [c19InvBlock17to24]
      rw [c19InvBlock25to31]
      rw [← c19InverseSumAdjoin]
      abel
#print axioms c19InvFor_sum_zero



