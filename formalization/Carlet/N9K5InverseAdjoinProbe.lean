import Carlet.N9K5InverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
open Polynomial
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
local instance : CharP (AdjoinRoot f9) 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f9)).injective 2
theorem n9K5InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f9*q) : (AdjoinRoot.mk f9 v)*(AdjoinRoot.mk f9 i)=1 := by
  have hd : f9 ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f9 (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f9 v)*(AdjoinRoot.mk f9 i)+1=0 := by simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f9 v)*(AdjoinRoot.mk f9 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f9)+1=0 := by
        calc
          (1:AdjoinRoot f9)+1=(2:AdjoinRoot f9) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f9) 2
      exact neg_eq_of_add_eq_zero_left ht
theorem n9K5InvAdjoin01 : (AdjoinRoot.mk f9 n9K5V01)*(AdjoinRoot.mk f9 n9K5I01)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv01
theorem n9K5InvAdjoin02 : (AdjoinRoot.mk f9 n9K5V02)*(AdjoinRoot.mk f9 n9K5I02)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv02
theorem n9K5InvAdjoin03 : (AdjoinRoot.mk f9 n9K5V03)*(AdjoinRoot.mk f9 n9K5I03)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv03
theorem n9K5InvAdjoin04 : (AdjoinRoot.mk f9 n9K5V04)*(AdjoinRoot.mk f9 n9K5I04)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv04
theorem n9K5InvAdjoin05 : (AdjoinRoot.mk f9 n9K5V05)*(AdjoinRoot.mk f9 n9K5I05)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv05
theorem n9K5InvAdjoin06 : (AdjoinRoot.mk f9 n9K5V06)*(AdjoinRoot.mk f9 n9K5I06)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv06
theorem n9K5InvAdjoin07 : (AdjoinRoot.mk f9 n9K5V07)*(AdjoinRoot.mk f9 n9K5I07)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv07
theorem n9K5InvAdjoin08 : (AdjoinRoot.mk f9 n9K5V08)*(AdjoinRoot.mk f9 n9K5I08)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv08
theorem n9K5InvAdjoin09 : (AdjoinRoot.mk f9 n9K5V09)*(AdjoinRoot.mk f9 n9K5I09)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv09
theorem n9K5InvAdjoin10 : (AdjoinRoot.mk f9 n9K5V10)*(AdjoinRoot.mk f9 n9K5I10)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv10
theorem n9K5InvAdjoin11 : (AdjoinRoot.mk f9 n9K5V11)*(AdjoinRoot.mk f9 n9K5I11)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv11
theorem n9K5InvAdjoin12 : (AdjoinRoot.mk f9 n9K5V12)*(AdjoinRoot.mk f9 n9K5I12)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv12
theorem n9K5InvAdjoin13 : (AdjoinRoot.mk f9 n9K5V13)*(AdjoinRoot.mk f9 n9K5I13)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv13
theorem n9K5InvAdjoin14 : (AdjoinRoot.mk f9 n9K5V14)*(AdjoinRoot.mk f9 n9K5I14)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv14
theorem n9K5InvAdjoin15 : (AdjoinRoot.mk f9 n9K5V15)*(AdjoinRoot.mk f9 n9K5I15)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv15
theorem n9K5InvAdjoin16 : (AdjoinRoot.mk f9 n9K5V16)*(AdjoinRoot.mk f9 n9K5I16)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv16
theorem n9K5InvAdjoin17 : (AdjoinRoot.mk f9 n9K5V17)*(AdjoinRoot.mk f9 n9K5I17)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv17
theorem n9K5InvAdjoin18 : (AdjoinRoot.mk f9 n9K5V18)*(AdjoinRoot.mk f9 n9K5I18)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv18
theorem n9K5InvAdjoin19 : (AdjoinRoot.mk f9 n9K5V19)*(AdjoinRoot.mk f9 n9K5I19)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv19
theorem n9K5InvAdjoin20 : (AdjoinRoot.mk f9 n9K5V20)*(AdjoinRoot.mk f9 n9K5I20)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv20
theorem n9K5InvAdjoin21 : (AdjoinRoot.mk f9 n9K5V21)*(AdjoinRoot.mk f9 n9K5I21)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv21
theorem n9K5InvAdjoin22 : (AdjoinRoot.mk f9 n9K5V22)*(AdjoinRoot.mk f9 n9K5I22)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv22
theorem n9K5InvAdjoin23 : (AdjoinRoot.mk f9 n9K5V23)*(AdjoinRoot.mk f9 n9K5I23)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv23
theorem n9K5InvAdjoin24 : (AdjoinRoot.mk f9 n9K5V24)*(AdjoinRoot.mk f9 n9K5I24)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv24
theorem n9K5InvAdjoin25 : (AdjoinRoot.mk f9 n9K5V25)*(AdjoinRoot.mk f9 n9K5I25)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv25
theorem n9K5InvAdjoin26 : (AdjoinRoot.mk f9 n9K5V26)*(AdjoinRoot.mk f9 n9K5I26)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv26
theorem n9K5InvAdjoin27 : (AdjoinRoot.mk f9 n9K5V27)*(AdjoinRoot.mk f9 n9K5I27)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv27
theorem n9K5InvAdjoin28 : (AdjoinRoot.mk f9 n9K5V28)*(AdjoinRoot.mk f9 n9K5I28)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv28
theorem n9K5InvAdjoin29 : (AdjoinRoot.mk f9 n9K5V29)*(AdjoinRoot.mk f9 n9K5I29)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv29
theorem n9K5InvAdjoin30 : (AdjoinRoot.mk f9 n9K5V30)*(AdjoinRoot.mk f9 n9K5I30)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv30
theorem n9K5InvAdjoin31 : (AdjoinRoot.mk f9 n9K5V31)*(AdjoinRoot.mk f9 n9K5I31)=1 := by exact n9K5InvAdjoin_of_poly n9K5Inv31
theorem n9K5InverseSumAdjoin : AdjoinRoot.mk f9 n9K5I01 + AdjoinRoot.mk f9 n9K5I02 + AdjoinRoot.mk f9 n9K5I03 + AdjoinRoot.mk f9 n9K5I04 + AdjoinRoot.mk f9 n9K5I05 + AdjoinRoot.mk f9 n9K5I06 + AdjoinRoot.mk f9 n9K5I07 + AdjoinRoot.mk f9 n9K5I08 + AdjoinRoot.mk f9 n9K5I09 + AdjoinRoot.mk f9 n9K5I10 + AdjoinRoot.mk f9 n9K5I11 + AdjoinRoot.mk f9 n9K5I12 + AdjoinRoot.mk f9 n9K5I13 + AdjoinRoot.mk f9 n9K5I14 + AdjoinRoot.mk f9 n9K5I15 + AdjoinRoot.mk f9 n9K5I16 + AdjoinRoot.mk f9 n9K5I17 + AdjoinRoot.mk f9 n9K5I18 + AdjoinRoot.mk f9 n9K5I19 + AdjoinRoot.mk f9 n9K5I20 + AdjoinRoot.mk f9 n9K5I21 + AdjoinRoot.mk f9 n9K5I22 + AdjoinRoot.mk f9 n9K5I23 + AdjoinRoot.mk f9 n9K5I24 + AdjoinRoot.mk f9 n9K5I25 + AdjoinRoot.mk f9 n9K5I26 + AdjoinRoot.mk f9 n9K5I27 + AdjoinRoot.mk f9 n9K5I28 + AdjoinRoot.mk f9 n9K5I29 + AdjoinRoot.mk f9 n9K5I30 + AdjoinRoot.mk f9 n9K5I31 = 0 := by
  have h := congrArg (AdjoinRoot.mk f9) n9K5InverseSum
  simpa only [map_add,map_zero] using h
#print axioms n9K5InvAdjoin01
#print axioms n9K5InvAdjoin31
#print axioms n9K5InverseSumAdjoin
