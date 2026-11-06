import Carlet.N19ModulusBridgeProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
local instance : CharP (AdjoinRoot f19) 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f19)).injective 2
theorem c19InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f19*q) : (AdjoinRoot.mk f19 v)*(AdjoinRoot.mk f19 i)=1 := by
  have hd : f19 ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f19 (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f19 v)*(AdjoinRoot.mk f19 i)+1=0 := by simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f19 v)*(AdjoinRoot.mk f19 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f19)+1=0 := by
        calc
          (1:AdjoinRoot f19)+1=(2:AdjoinRoot f19) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f19) 2
      exact neg_eq_of_add_eq_zero_left ht
theorem c19InvAdjoin01 : (AdjoinRoot.mk f19 c19V01)*(AdjoinRoot.mk f19 c19I01)=1 := by exact c19InvAdjoin_of_poly c19Inv01
theorem c19InvAdjoin02 : (AdjoinRoot.mk f19 c19V02)*(AdjoinRoot.mk f19 c19I02)=1 := by exact c19InvAdjoin_of_poly c19Inv02
theorem c19InvAdjoin03 : (AdjoinRoot.mk f19 c19V03)*(AdjoinRoot.mk f19 c19I03)=1 := by exact c19InvAdjoin_of_poly c19Inv03
theorem c19InvAdjoin04 : (AdjoinRoot.mk f19 c19V04)*(AdjoinRoot.mk f19 c19I04)=1 := by exact c19InvAdjoin_of_poly c19Inv04
theorem c19InvAdjoin05 : (AdjoinRoot.mk f19 c19V05)*(AdjoinRoot.mk f19 c19I05)=1 := by exact c19InvAdjoin_of_poly c19Inv05
theorem c19InvAdjoin06 : (AdjoinRoot.mk f19 c19V06)*(AdjoinRoot.mk f19 c19I06)=1 := by exact c19InvAdjoin_of_poly c19Inv06
theorem c19InvAdjoin07 : (AdjoinRoot.mk f19 c19V07)*(AdjoinRoot.mk f19 c19I07)=1 := by exact c19InvAdjoin_of_poly c19Inv07
theorem c19InvAdjoin08 : (AdjoinRoot.mk f19 c19V08)*(AdjoinRoot.mk f19 c19I08)=1 := by exact c19InvAdjoin_of_poly c19Inv08
theorem c19InvAdjoin09 : (AdjoinRoot.mk f19 c19V09)*(AdjoinRoot.mk f19 c19I09)=1 := by exact c19InvAdjoin_of_poly c19Inv09
theorem c19InvAdjoin10 : (AdjoinRoot.mk f19 c19V10)*(AdjoinRoot.mk f19 c19I10)=1 := by exact c19InvAdjoin_of_poly c19Inv10
theorem c19InvAdjoin11 : (AdjoinRoot.mk f19 c19V11)*(AdjoinRoot.mk f19 c19I11)=1 := by exact c19InvAdjoin_of_poly c19Inv11
theorem c19InvAdjoin12 : (AdjoinRoot.mk f19 c19V12)*(AdjoinRoot.mk f19 c19I12)=1 := by exact c19InvAdjoin_of_poly c19Inv12
theorem c19InvAdjoin13 : (AdjoinRoot.mk f19 c19V13)*(AdjoinRoot.mk f19 c19I13)=1 := by exact c19InvAdjoin_of_poly c19Inv13
theorem c19InvAdjoin14 : (AdjoinRoot.mk f19 c19V14)*(AdjoinRoot.mk f19 c19I14)=1 := by exact c19InvAdjoin_of_poly c19Inv14
theorem c19InvAdjoin15 : (AdjoinRoot.mk f19 c19V15)*(AdjoinRoot.mk f19 c19I15)=1 := by exact c19InvAdjoin_of_poly c19Inv15
theorem c19InvAdjoin16 : (AdjoinRoot.mk f19 c19V16)*(AdjoinRoot.mk f19 c19I16)=1 := by exact c19InvAdjoin_of_poly c19Inv16
theorem c19InvAdjoin17 : (AdjoinRoot.mk f19 c19V17)*(AdjoinRoot.mk f19 c19I17)=1 := by exact c19InvAdjoin_of_poly c19Inv17
theorem c19InvAdjoin18 : (AdjoinRoot.mk f19 c19V18)*(AdjoinRoot.mk f19 c19I18)=1 := by exact c19InvAdjoin_of_poly c19Inv18
theorem c19InvAdjoin19 : (AdjoinRoot.mk f19 c19V19)*(AdjoinRoot.mk f19 c19I19)=1 := by exact c19InvAdjoin_of_poly c19Inv19
theorem c19InvAdjoin20 : (AdjoinRoot.mk f19 c19V20)*(AdjoinRoot.mk f19 c19I20)=1 := by exact c19InvAdjoin_of_poly c19Inv20
theorem c19InvAdjoin21 : (AdjoinRoot.mk f19 c19V21)*(AdjoinRoot.mk f19 c19I21)=1 := by exact c19InvAdjoin_of_poly c19Inv21
theorem c19InvAdjoin22 : (AdjoinRoot.mk f19 c19V22)*(AdjoinRoot.mk f19 c19I22)=1 := by exact c19InvAdjoin_of_poly c19Inv22
theorem c19InvAdjoin23 : (AdjoinRoot.mk f19 c19V23)*(AdjoinRoot.mk f19 c19I23)=1 := by exact c19InvAdjoin_of_poly c19Inv23
theorem c19InvAdjoin24 : (AdjoinRoot.mk f19 c19V24)*(AdjoinRoot.mk f19 c19I24)=1 := by exact c19InvAdjoin_of_poly c19Inv24
theorem c19InvAdjoin25 : (AdjoinRoot.mk f19 c19V25)*(AdjoinRoot.mk f19 c19I25)=1 := by exact c19InvAdjoin_of_poly c19Inv25
theorem c19InvAdjoin26 : (AdjoinRoot.mk f19 c19V26)*(AdjoinRoot.mk f19 c19I26)=1 := by exact c19InvAdjoin_of_poly c19Inv26
theorem c19InvAdjoin27 : (AdjoinRoot.mk f19 c19V27)*(AdjoinRoot.mk f19 c19I27)=1 := by exact c19InvAdjoin_of_poly c19Inv27
theorem c19InvAdjoin28 : (AdjoinRoot.mk f19 c19V28)*(AdjoinRoot.mk f19 c19I28)=1 := by exact c19InvAdjoin_of_poly c19Inv28
theorem c19InvAdjoin29 : (AdjoinRoot.mk f19 c19V29)*(AdjoinRoot.mk f19 c19I29)=1 := by exact c19InvAdjoin_of_poly c19Inv29
theorem c19InvAdjoin30 : (AdjoinRoot.mk f19 c19V30)*(AdjoinRoot.mk f19 c19I30)=1 := by exact c19InvAdjoin_of_poly c19Inv30
theorem c19InvAdjoin31 : (AdjoinRoot.mk f19 c19V31)*(AdjoinRoot.mk f19 c19I31)=1 := by exact c19InvAdjoin_of_poly c19Inv31
theorem c19InverseSumAdjoin : AdjoinRoot.mk f19 c19I01 + AdjoinRoot.mk f19 c19I02 + AdjoinRoot.mk f19 c19I03 + AdjoinRoot.mk f19 c19I04 + AdjoinRoot.mk f19 c19I05 + AdjoinRoot.mk f19 c19I06 + AdjoinRoot.mk f19 c19I07 + AdjoinRoot.mk f19 c19I08 + AdjoinRoot.mk f19 c19I09 + AdjoinRoot.mk f19 c19I10 + AdjoinRoot.mk f19 c19I11 + AdjoinRoot.mk f19 c19I12 + AdjoinRoot.mk f19 c19I13 + AdjoinRoot.mk f19 c19I14 + AdjoinRoot.mk f19 c19I15 + AdjoinRoot.mk f19 c19I16 + AdjoinRoot.mk f19 c19I17 + AdjoinRoot.mk f19 c19I18 + AdjoinRoot.mk f19 c19I19 + AdjoinRoot.mk f19 c19I20 + AdjoinRoot.mk f19 c19I21 + AdjoinRoot.mk f19 c19I22 + AdjoinRoot.mk f19 c19I23 + AdjoinRoot.mk f19 c19I24 + AdjoinRoot.mk f19 c19I25 + AdjoinRoot.mk f19 c19I26 + AdjoinRoot.mk f19 c19I27 + AdjoinRoot.mk f19 c19I28 + AdjoinRoot.mk f19 c19I29 + AdjoinRoot.mk f19 c19I30 + AdjoinRoot.mk f19 c19I31=0 := by
  have h:=congrArg (AdjoinRoot.mk f19) c19InverseSum
  simpa only [map_add,map_zero] using h
#print axioms c19InvAdjoin01
#print axioms c19InverseSumAdjoin
