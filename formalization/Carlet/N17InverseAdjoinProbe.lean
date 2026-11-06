import Carlet.N17N19InverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
local instance : CharP (AdjoinRoot f17) 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f17)).injective 2
theorem c17InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f17*q) : (AdjoinRoot.mk f17 v)*(AdjoinRoot.mk f17 i)=1 := by
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
theorem c17InvAdjoin01 : (AdjoinRoot.mk f17 c17V01)*(AdjoinRoot.mk f17 c17I01)=1 := by exact c17InvAdjoin_of_poly c17Inv01
theorem c17InvAdjoin02 : (AdjoinRoot.mk f17 c17V02)*(AdjoinRoot.mk f17 c17I02)=1 := by exact c17InvAdjoin_of_poly c17Inv02
theorem c17InvAdjoin03 : (AdjoinRoot.mk f17 c17V03)*(AdjoinRoot.mk f17 c17I03)=1 := by exact c17InvAdjoin_of_poly c17Inv03
theorem c17InvAdjoin04 : (AdjoinRoot.mk f17 c17V04)*(AdjoinRoot.mk f17 c17I04)=1 := by exact c17InvAdjoin_of_poly c17Inv04
theorem c17InvAdjoin05 : (AdjoinRoot.mk f17 c17V05)*(AdjoinRoot.mk f17 c17I05)=1 := by exact c17InvAdjoin_of_poly c17Inv05
theorem c17InvAdjoin06 : (AdjoinRoot.mk f17 c17V06)*(AdjoinRoot.mk f17 c17I06)=1 := by exact c17InvAdjoin_of_poly c17Inv06
theorem c17InvAdjoin07 : (AdjoinRoot.mk f17 c17V07)*(AdjoinRoot.mk f17 c17I07)=1 := by exact c17InvAdjoin_of_poly c17Inv07
theorem c17InvAdjoin08 : (AdjoinRoot.mk f17 c17V08)*(AdjoinRoot.mk f17 c17I08)=1 := by exact c17InvAdjoin_of_poly c17Inv08
theorem c17InvAdjoin09 : (AdjoinRoot.mk f17 c17V09)*(AdjoinRoot.mk f17 c17I09)=1 := by exact c17InvAdjoin_of_poly c17Inv09
theorem c17InvAdjoin10 : (AdjoinRoot.mk f17 c17V10)*(AdjoinRoot.mk f17 c17I10)=1 := by exact c17InvAdjoin_of_poly c17Inv10
theorem c17InvAdjoin11 : (AdjoinRoot.mk f17 c17V11)*(AdjoinRoot.mk f17 c17I11)=1 := by exact c17InvAdjoin_of_poly c17Inv11
theorem c17InvAdjoin12 : (AdjoinRoot.mk f17 c17V12)*(AdjoinRoot.mk f17 c17I12)=1 := by exact c17InvAdjoin_of_poly c17Inv12
theorem c17InvAdjoin13 : (AdjoinRoot.mk f17 c17V13)*(AdjoinRoot.mk f17 c17I13)=1 := by exact c17InvAdjoin_of_poly c17Inv13
theorem c17InvAdjoin14 : (AdjoinRoot.mk f17 c17V14)*(AdjoinRoot.mk f17 c17I14)=1 := by exact c17InvAdjoin_of_poly c17Inv14
theorem c17InvAdjoin15 : (AdjoinRoot.mk f17 c17V15)*(AdjoinRoot.mk f17 c17I15)=1 := by exact c17InvAdjoin_of_poly c17Inv15
theorem c17InvAdjoin16 : (AdjoinRoot.mk f17 c17V16)*(AdjoinRoot.mk f17 c17I16)=1 := by exact c17InvAdjoin_of_poly c17Inv16
theorem c17InvAdjoin17 : (AdjoinRoot.mk f17 c17V17)*(AdjoinRoot.mk f17 c17I17)=1 := by exact c17InvAdjoin_of_poly c17Inv17
theorem c17InvAdjoin18 : (AdjoinRoot.mk f17 c17V18)*(AdjoinRoot.mk f17 c17I18)=1 := by exact c17InvAdjoin_of_poly c17Inv18
theorem c17InvAdjoin19 : (AdjoinRoot.mk f17 c17V19)*(AdjoinRoot.mk f17 c17I19)=1 := by exact c17InvAdjoin_of_poly c17Inv19
theorem c17InvAdjoin20 : (AdjoinRoot.mk f17 c17V20)*(AdjoinRoot.mk f17 c17I20)=1 := by exact c17InvAdjoin_of_poly c17Inv20
theorem c17InvAdjoin21 : (AdjoinRoot.mk f17 c17V21)*(AdjoinRoot.mk f17 c17I21)=1 := by exact c17InvAdjoin_of_poly c17Inv21
theorem c17InvAdjoin22 : (AdjoinRoot.mk f17 c17V22)*(AdjoinRoot.mk f17 c17I22)=1 := by exact c17InvAdjoin_of_poly c17Inv22
theorem c17InvAdjoin23 : (AdjoinRoot.mk f17 c17V23)*(AdjoinRoot.mk f17 c17I23)=1 := by exact c17InvAdjoin_of_poly c17Inv23
theorem c17InvAdjoin24 : (AdjoinRoot.mk f17 c17V24)*(AdjoinRoot.mk f17 c17I24)=1 := by exact c17InvAdjoin_of_poly c17Inv24
theorem c17InvAdjoin25 : (AdjoinRoot.mk f17 c17V25)*(AdjoinRoot.mk f17 c17I25)=1 := by exact c17InvAdjoin_of_poly c17Inv25
theorem c17InvAdjoin26 : (AdjoinRoot.mk f17 c17V26)*(AdjoinRoot.mk f17 c17I26)=1 := by exact c17InvAdjoin_of_poly c17Inv26
theorem c17InvAdjoin27 : (AdjoinRoot.mk f17 c17V27)*(AdjoinRoot.mk f17 c17I27)=1 := by exact c17InvAdjoin_of_poly c17Inv27
theorem c17InvAdjoin28 : (AdjoinRoot.mk f17 c17V28)*(AdjoinRoot.mk f17 c17I28)=1 := by exact c17InvAdjoin_of_poly c17Inv28
theorem c17InvAdjoin29 : (AdjoinRoot.mk f17 c17V29)*(AdjoinRoot.mk f17 c17I29)=1 := by exact c17InvAdjoin_of_poly c17Inv29
theorem c17InvAdjoin30 : (AdjoinRoot.mk f17 c17V30)*(AdjoinRoot.mk f17 c17I30)=1 := by exact c17InvAdjoin_of_poly c17Inv30
theorem c17InvAdjoin31 : (AdjoinRoot.mk f17 c17V31)*(AdjoinRoot.mk f17 c17I31)=1 := by exact c17InvAdjoin_of_poly c17Inv31
theorem c17InverseSumAdjoin : AdjoinRoot.mk f17 c17I01 + AdjoinRoot.mk f17 c17I02 + AdjoinRoot.mk f17 c17I03 + AdjoinRoot.mk f17 c17I04 + AdjoinRoot.mk f17 c17I05 + AdjoinRoot.mk f17 c17I06 + AdjoinRoot.mk f17 c17I07 + AdjoinRoot.mk f17 c17I08 + AdjoinRoot.mk f17 c17I09 + AdjoinRoot.mk f17 c17I10 + AdjoinRoot.mk f17 c17I11 + AdjoinRoot.mk f17 c17I12 + AdjoinRoot.mk f17 c17I13 + AdjoinRoot.mk f17 c17I14 + AdjoinRoot.mk f17 c17I15 + AdjoinRoot.mk f17 c17I16 + AdjoinRoot.mk f17 c17I17 + AdjoinRoot.mk f17 c17I18 + AdjoinRoot.mk f17 c17I19 + AdjoinRoot.mk f17 c17I20 + AdjoinRoot.mk f17 c17I21 + AdjoinRoot.mk f17 c17I22 + AdjoinRoot.mk f17 c17I23 + AdjoinRoot.mk f17 c17I24 + AdjoinRoot.mk f17 c17I25 + AdjoinRoot.mk f17 c17I26 + AdjoinRoot.mk f17 c17I27 + AdjoinRoot.mk f17 c17I28 + AdjoinRoot.mk f17 c17I29 + AdjoinRoot.mk f17 c17I30 + AdjoinRoot.mk f17 c17I31=0 := by
  have h:=congrArg (AdjoinRoot.mk f17) c17InverseSum
  simpa only [map_add,map_zero] using h
#print axioms c17InvAdjoin01
#print axioms c17InverseSumAdjoin
