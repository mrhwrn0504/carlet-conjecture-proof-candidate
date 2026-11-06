import Carlet.N23K5InverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial
noncomputable section
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩
local instance : CharP (AdjoinRoot f23) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f23)).injective 2

theorem n23K5InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f23*q) :
    (AdjoinRoot.mk f23 v)*(AdjoinRoot.mk f23 i)=1 := by
  have hd : f23 ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f23 (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f23 v)*(AdjoinRoot.mk f23 i)+1=0 := by
    simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f23 v)*(AdjoinRoot.mk f23 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f23)+1=0 := by
        calc
          (1:AdjoinRoot f23)+1=(2:AdjoinRoot f23) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f23) 2
      exact neg_eq_of_add_eq_zero_left ht

theorem n23K5InvAdjoin01 :
    (AdjoinRoot.mk f23 n23K5V01)*(AdjoinRoot.mk f23 n23K5I01)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv01
theorem n23K5InvAdjoin02 :
    (AdjoinRoot.mk f23 n23K5V02)*(AdjoinRoot.mk f23 n23K5I02)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv02
theorem n23K5InvAdjoin03 :
    (AdjoinRoot.mk f23 n23K5V03)*(AdjoinRoot.mk f23 n23K5I03)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv03
theorem n23K5InvAdjoin04 :
    (AdjoinRoot.mk f23 n23K5V04)*(AdjoinRoot.mk f23 n23K5I04)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv04
theorem n23K5InvAdjoin05 :
    (AdjoinRoot.mk f23 n23K5V05)*(AdjoinRoot.mk f23 n23K5I05)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv05
theorem n23K5InvAdjoin06 :
    (AdjoinRoot.mk f23 n23K5V06)*(AdjoinRoot.mk f23 n23K5I06)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv06
theorem n23K5InvAdjoin07 :
    (AdjoinRoot.mk f23 n23K5V07)*(AdjoinRoot.mk f23 n23K5I07)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv07
theorem n23K5InvAdjoin08 :
    (AdjoinRoot.mk f23 n23K5V08)*(AdjoinRoot.mk f23 n23K5I08)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv08
theorem n23K5InvAdjoin09 :
    (AdjoinRoot.mk f23 n23K5V09)*(AdjoinRoot.mk f23 n23K5I09)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv09
theorem n23K5InvAdjoin10 :
    (AdjoinRoot.mk f23 n23K5V10)*(AdjoinRoot.mk f23 n23K5I10)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv10
theorem n23K5InvAdjoin11 :
    (AdjoinRoot.mk f23 n23K5V11)*(AdjoinRoot.mk f23 n23K5I11)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv11
theorem n23K5InvAdjoin12 :
    (AdjoinRoot.mk f23 n23K5V12)*(AdjoinRoot.mk f23 n23K5I12)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv12
theorem n23K5InvAdjoin13 :
    (AdjoinRoot.mk f23 n23K5V13)*(AdjoinRoot.mk f23 n23K5I13)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv13
theorem n23K5InvAdjoin14 :
    (AdjoinRoot.mk f23 n23K5V14)*(AdjoinRoot.mk f23 n23K5I14)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv14
theorem n23K5InvAdjoin15 :
    (AdjoinRoot.mk f23 n23K5V15)*(AdjoinRoot.mk f23 n23K5I15)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv15
theorem n23K5InvAdjoin16 :
    (AdjoinRoot.mk f23 n23K5V16)*(AdjoinRoot.mk f23 n23K5I16)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv16
theorem n23K5InvAdjoin17 :
    (AdjoinRoot.mk f23 n23K5V17)*(AdjoinRoot.mk f23 n23K5I17)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv17
theorem n23K5InvAdjoin18 :
    (AdjoinRoot.mk f23 n23K5V18)*(AdjoinRoot.mk f23 n23K5I18)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv18
theorem n23K5InvAdjoin19 :
    (AdjoinRoot.mk f23 n23K5V19)*(AdjoinRoot.mk f23 n23K5I19)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv19
theorem n23K5InvAdjoin20 :
    (AdjoinRoot.mk f23 n23K5V20)*(AdjoinRoot.mk f23 n23K5I20)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv20
theorem n23K5InvAdjoin21 :
    (AdjoinRoot.mk f23 n23K5V21)*(AdjoinRoot.mk f23 n23K5I21)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv21
theorem n23K5InvAdjoin22 :
    (AdjoinRoot.mk f23 n23K5V22)*(AdjoinRoot.mk f23 n23K5I22)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv22
theorem n23K5InvAdjoin23 :
    (AdjoinRoot.mk f23 n23K5V23)*(AdjoinRoot.mk f23 n23K5I23)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv23
theorem n23K5InvAdjoin24 :
    (AdjoinRoot.mk f23 n23K5V24)*(AdjoinRoot.mk f23 n23K5I24)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv24
theorem n23K5InvAdjoin25 :
    (AdjoinRoot.mk f23 n23K5V25)*(AdjoinRoot.mk f23 n23K5I25)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv25
theorem n23K5InvAdjoin26 :
    (AdjoinRoot.mk f23 n23K5V26)*(AdjoinRoot.mk f23 n23K5I26)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv26
theorem n23K5InvAdjoin27 :
    (AdjoinRoot.mk f23 n23K5V27)*(AdjoinRoot.mk f23 n23K5I27)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv27
theorem n23K5InvAdjoin28 :
    (AdjoinRoot.mk f23 n23K5V28)*(AdjoinRoot.mk f23 n23K5I28)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv28
theorem n23K5InvAdjoin29 :
    (AdjoinRoot.mk f23 n23K5V29)*(AdjoinRoot.mk f23 n23K5I29)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv29
theorem n23K5InvAdjoin30 :
    (AdjoinRoot.mk f23 n23K5V30)*(AdjoinRoot.mk f23 n23K5I30)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv30
theorem n23K5InvAdjoin31 :
    (AdjoinRoot.mk f23 n23K5V31)*(AdjoinRoot.mk f23 n23K5I31)=1 :=
  n23K5InvAdjoin_of_poly n23K5Inv31

theorem n23K5InverseSumAdjoin :
    (AdjoinRoot.mk f23 n23K5I01 + AdjoinRoot.mk f23 n23K5I02 +
     AdjoinRoot.mk f23 n23K5I03 + AdjoinRoot.mk f23 n23K5I04 +
     AdjoinRoot.mk f23 n23K5I05 + AdjoinRoot.mk f23 n23K5I06 +
     AdjoinRoot.mk f23 n23K5I07 + AdjoinRoot.mk f23 n23K5I08 +
     AdjoinRoot.mk f23 n23K5I09 + AdjoinRoot.mk f23 n23K5I10 +
     AdjoinRoot.mk f23 n23K5I11 + AdjoinRoot.mk f23 n23K5I12 +
     AdjoinRoot.mk f23 n23K5I13 + AdjoinRoot.mk f23 n23K5I14 +
     AdjoinRoot.mk f23 n23K5I15 + AdjoinRoot.mk f23 n23K5I16 +
     AdjoinRoot.mk f23 n23K5I17 + AdjoinRoot.mk f23 n23K5I18 +
     AdjoinRoot.mk f23 n23K5I19 + AdjoinRoot.mk f23 n23K5I20 +
     AdjoinRoot.mk f23 n23K5I21 + AdjoinRoot.mk f23 n23K5I22 +
     AdjoinRoot.mk f23 n23K5I23 + AdjoinRoot.mk f23 n23K5I24 +
     AdjoinRoot.mk f23 n23K5I25 + AdjoinRoot.mk f23 n23K5I26 +
     AdjoinRoot.mk f23 n23K5I27 + AdjoinRoot.mk f23 n23K5I28 +
     AdjoinRoot.mk f23 n23K5I29 + AdjoinRoot.mk f23 n23K5I30 +
     AdjoinRoot.mk f23 n23K5I31) = 0 := by
  have h := congrArg (AdjoinRoot.mk f23) n23K5InverseSum
  simpa only [map_add, map_zero] using h

#print axioms n23K5InvAdjoin_of_poly
#print axioms n23K5InverseSumAdjoin
