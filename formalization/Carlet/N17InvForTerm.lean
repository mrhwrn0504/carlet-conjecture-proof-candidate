import Carlet.N17DecodeInverseProbe
import Carlet.N17InverseAdjoinProbe
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩

def c17InvFor (i : Fin 31) : AdjoinRoot f17 := AdjoinRoot.mk f17 (match i.val with
  | 0 => c17I01
  | 1 => c17I02
  | 2 => c17I03
  | 3 => c17I04
  | 4 => c17I05
  | 5 => c17I06
  | 6 => c17I07
  | 7 => c17I08
  | 8 => c17I09
  | 9 => c17I10
  | 10 => c17I11
  | 11 => c17I12
  | 12 => c17I13
  | 13 => c17I14
  | 14 => c17I15
  | 15 => c17I16
  | 16 => c17I17
  | 17 => c17I18
  | 18 => c17I19
  | 19 => c17I20
  | 20 => c17I21
  | 21 => c17I22
  | 22 => c17I23
  | 23 => c17I24
  | 24 => c17I25
  | 25 => c17I26
  | 26 => c17I27
  | 27 => c17I28
  | 28 => c17I29
  | 29 => c17I30
  | 30 => c17I31
  | _ => 0)

theorem c17DecodeInvSucc (i : Fin 31) : (c17SubsetSum (subsetDecode17 i.succ))⁻¹ = c17InvFor i := by
  classical
  fin_cases i
  case «0» => simpa [c17InvFor] using c17DecodeInv01
  case «1» => simpa [c17InvFor] using c17DecodeInv02
  case «2» => simpa [c17InvFor] using c17DecodeInv03
  case «3» => simpa [c17InvFor] using c17DecodeInv04
  case «4» => simpa [c17InvFor] using c17DecodeInv05
  case «5» => simpa [c17InvFor] using c17DecodeInv06
  case «6» => simpa [c17InvFor] using c17DecodeInv07
  case «7» => simpa [c17InvFor] using c17DecodeInv08
  case «8» => simpa [c17InvFor] using c17DecodeInv09
  case «9» => simpa [c17InvFor] using c17DecodeInv10
  case «10» => simpa [c17InvFor] using c17DecodeInv11
  case «11» => simpa [c17InvFor] using c17DecodeInv12
  case «12» => simpa [c17InvFor] using c17DecodeInv13
  case «13» => simpa [c17InvFor] using c17DecodeInv14
  case «14» => simpa [c17InvFor] using c17DecodeInv15
  case «15» => simpa [c17InvFor] using c17DecodeInv16
  case «16» => simpa [c17InvFor] using c17DecodeInv17
  case «17» => simpa [c17InvFor] using c17DecodeInv18
  case «18» => simpa [c17InvFor] using c17DecodeInv19
  case «19» => simpa [c17InvFor] using c17DecodeInv20
  case «20» => simpa [c17InvFor] using c17DecodeInv21
  case «21» => simpa [c17InvFor] using c17DecodeInv22
  case «22» => simpa [c17InvFor] using c17DecodeInv23
  case «23» => simpa [c17InvFor] using c17DecodeInv24
  case «24» => simpa [c17InvFor] using c17DecodeInv25
  case «25» => simpa [c17InvFor] using c17DecodeInv26
  case «26» => simpa [c17InvFor] using c17DecodeInv27
  case «27» => simpa [c17InvFor] using c17DecodeInv28
  case «28» => simpa [c17InvFor] using c17DecodeInv29
  case «29» => simpa [c17InvFor] using c17DecodeInv30
  case «30» => simpa [c17InvFor] using c17DecodeInv31

#print axioms c17DecodeInvSucc

theorem c17InvBlock01to08 :
    (∑ i : Fin 8, c17InvFor (Fin.castAdd 23 i)) =
      AdjoinRoot.mk f17 c17I01 + AdjoinRoot.mk f17 c17I02 + AdjoinRoot.mk f17 c17I03 + AdjoinRoot.mk f17 c17I04 +
      AdjoinRoot.mk f17 c17I05 + AdjoinRoot.mk f17 c17I06 + AdjoinRoot.mk f17 c17I07 + AdjoinRoot.mk f17 c17I08 := by
  simp [Fin.sum_univ_succ, c17InvFor, Fin.val_castAdd]
  ring

theorem c17InvBlock09to16 :
    (∑ i : Fin 8, c17InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) =
      AdjoinRoot.mk f17 c17I09 + AdjoinRoot.mk f17 c17I10 + AdjoinRoot.mk f17 c17I11 + AdjoinRoot.mk f17 c17I12 +
      AdjoinRoot.mk f17 c17I13 + AdjoinRoot.mk f17 c17I14 + AdjoinRoot.mk f17 c17I15 + AdjoinRoot.mk f17 c17I16 := by
  simp [Fin.sum_univ_succ, c17InvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem c17InvBlock17to24 :
    (∑ i : Fin 8, c17InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) =
      AdjoinRoot.mk f17 c17I17 + AdjoinRoot.mk f17 c17I18 + AdjoinRoot.mk f17 c17I19 + AdjoinRoot.mk f17 c17I20 +
      AdjoinRoot.mk f17 c17I21 + AdjoinRoot.mk f17 c17I22 + AdjoinRoot.mk f17 c17I23 + AdjoinRoot.mk f17 c17I24 := by
  simp [Fin.sum_univ_succ, c17InvFor, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem c17InvBlock25to31 :
    (∑ i : Fin 7, c17InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i)))) =
      AdjoinRoot.mk f17 c17I25 + AdjoinRoot.mk f17 c17I26 + AdjoinRoot.mk f17 c17I27 + AdjoinRoot.mk f17 c17I28 +
      AdjoinRoot.mk f17 c17I29 + AdjoinRoot.mk f17 c17I30 + AdjoinRoot.mk f17 c17I31 := by
  simp [Fin.sum_univ_succ, c17InvFor, Fin.val_natAdd]
  ring

theorem c17InvFor_sum_zero : (∑ i : Fin 31, c17InvFor i) = 0 := by
  calc
    (∑ i : Fin 31, c17InvFor i) =
        (∑ i : Fin 8, c17InvFor (Fin.castAdd 23 i)) + (∑ j : Fin 23, c17InvFor (Fin.natAdd 8 j)) := by
      exact Fin.sum_univ_add (a := 8) (b := 23) (f := c17InvFor)
    _ = (∑ i : Fin 8, c17InvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, c17InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         (∑ j : Fin 15, c17InvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 15)
        (f := fun j : Fin 23 => c17InvFor (Fin.natAdd 8 j))
      simpa using hsplit
    _ = (∑ i : Fin 8, c17InvFor (Fin.castAdd 23 i)) +
        ((∑ i : Fin 8, c17InvFor (Fin.natAdd 8 (Fin.castAdd 15 i))) +
         ((∑ i : Fin 8, c17InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 7 i)))) +
          (∑ j : Fin 7, c17InvFor (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 j)))))) := by
      have hsplit := Fin.sum_univ_add (a := 8) (b := 7)
        (f := fun j : Fin 15 => c17InvFor (Fin.natAdd 8 (Fin.natAdd 8 j)))
      simpa using hsplit
    _ = 0 := by
      rw [c17InvBlock01to08]
      rw [c17InvBlock09to16]
      rw [c17InvBlock17to24]
      rw [c17InvBlock25to31]
      rw [← c17InverseSumAdjoin]
      abel
#print axioms c17InvFor_sum_zero



