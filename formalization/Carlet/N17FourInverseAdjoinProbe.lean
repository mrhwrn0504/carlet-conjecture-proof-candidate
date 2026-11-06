import Carlet.N17FourInverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
local instance instCharPAdjoinRootF17Four : CharP (AdjoinRoot f17) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f17)).injective 2
theorem e17InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f17*q) : (AdjoinRoot.mk f17 v)*(AdjoinRoot.mk f17 i)=1 := by
  have hd : f17 ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f17 (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f17 v)*(AdjoinRoot.mk f17 i)+1=0 := by simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f17 v)*(AdjoinRoot.mk f17 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f17)+1=0 := by
        calc
          (1:AdjoinRoot f17)+1=(2:AdjoinRoot f17) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f17) 2
      exact neg_eq_of_add_eq_zero_left ht
theorem e17InvAdjoin01 : (AdjoinRoot.mk f17 e17V01)*(AdjoinRoot.mk f17 e17I01)=1 := by exact e17InvAdjoin_of_poly e17Inv01
theorem e17InvAdjoin02 : (AdjoinRoot.mk f17 e17V02)*(AdjoinRoot.mk f17 e17I02)=1 := by exact e17InvAdjoin_of_poly e17Inv02
theorem e17InvAdjoin03 : (AdjoinRoot.mk f17 e17V03)*(AdjoinRoot.mk f17 e17I03)=1 := by exact e17InvAdjoin_of_poly e17Inv03
theorem e17InvAdjoin04 : (AdjoinRoot.mk f17 e17V04)*(AdjoinRoot.mk f17 e17I04)=1 := by exact e17InvAdjoin_of_poly e17Inv04
theorem e17InvAdjoin05 : (AdjoinRoot.mk f17 e17V05)*(AdjoinRoot.mk f17 e17I05)=1 := by exact e17InvAdjoin_of_poly e17Inv05
theorem e17InvAdjoin06 : (AdjoinRoot.mk f17 e17V06)*(AdjoinRoot.mk f17 e17I06)=1 := by exact e17InvAdjoin_of_poly e17Inv06
theorem e17InvAdjoin07 : (AdjoinRoot.mk f17 e17V07)*(AdjoinRoot.mk f17 e17I07)=1 := by exact e17InvAdjoin_of_poly e17Inv07
theorem e17InvAdjoin08 : (AdjoinRoot.mk f17 e17V08)*(AdjoinRoot.mk f17 e17I08)=1 := by exact e17InvAdjoin_of_poly e17Inv08
theorem e17InvAdjoin09 : (AdjoinRoot.mk f17 e17V09)*(AdjoinRoot.mk f17 e17I09)=1 := by exact e17InvAdjoin_of_poly e17Inv09
theorem e17InvAdjoin10 : (AdjoinRoot.mk f17 e17V10)*(AdjoinRoot.mk f17 e17I10)=1 := by exact e17InvAdjoin_of_poly e17Inv10
theorem e17InvAdjoin17 : (AdjoinRoot.mk f17 e17V11)*(AdjoinRoot.mk f17 e17I11)=1 := by exact e17InvAdjoin_of_poly e17Inv11
theorem e17InvAdjoin12 : (AdjoinRoot.mk f17 e17V12)*(AdjoinRoot.mk f17 e17I12)=1 := by exact e17InvAdjoin_of_poly e17Inv12
theorem e17InvAdjoin13 : (AdjoinRoot.mk f17 e17V13)*(AdjoinRoot.mk f17 e17I13)=1 := by exact e17InvAdjoin_of_poly e17Inv13
theorem e17InvAdjoin14 : (AdjoinRoot.mk f17 e17V14)*(AdjoinRoot.mk f17 e17I14)=1 := by exact e17InvAdjoin_of_poly e17Inv14
theorem e17InvAdjoin15 : (AdjoinRoot.mk f17 e17V15)*(AdjoinRoot.mk f17 e17I15)=1 := by exact e17InvAdjoin_of_poly e17Inv15
theorem e17InverseSumAdjoin : AdjoinRoot.mk f17 e17I01 + AdjoinRoot.mk f17 e17I02 + AdjoinRoot.mk f17 e17I03 + AdjoinRoot.mk f17 e17I04 + AdjoinRoot.mk f17 e17I05 + AdjoinRoot.mk f17 e17I06 + AdjoinRoot.mk f17 e17I07 + AdjoinRoot.mk f17 e17I08 + AdjoinRoot.mk f17 e17I09 + AdjoinRoot.mk f17 e17I10 + AdjoinRoot.mk f17 e17I11 + AdjoinRoot.mk f17 e17I12 + AdjoinRoot.mk f17 e17I13 + AdjoinRoot.mk f17 e17I14 + AdjoinRoot.mk f17 e17I15 = 0 := by
  have h := congrArg (AdjoinRoot.mk f17) e17InverseSum
  simpa only [map_add,map_zero] using h
#print axioms e17InvAdjoin01
#print axioms e17InverseSumAdjoin
