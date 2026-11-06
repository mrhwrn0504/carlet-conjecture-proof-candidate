import Carlet.N19FourInverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
local instance instCharPAdjoinRootF19Four : CharP (AdjoinRoot f19) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f19)).injective 2
theorem e19InvAdjoin_of_poly {v i q : P19} (h : v*i+1=f19*q) : (AdjoinRoot.mk f19 v)*(AdjoinRoot.mk f19 i)=1 := by
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
theorem e19InvAdjoin01 : (AdjoinRoot.mk f19 e19V01)*(AdjoinRoot.mk f19 e19I01)=1 := by exact e19InvAdjoin_of_poly e19Inv01
theorem e19InvAdjoin02 : (AdjoinRoot.mk f19 e19V02)*(AdjoinRoot.mk f19 e19I02)=1 := by exact e19InvAdjoin_of_poly e19Inv02
theorem e19InvAdjoin03 : (AdjoinRoot.mk f19 e19V03)*(AdjoinRoot.mk f19 e19I03)=1 := by exact e19InvAdjoin_of_poly e19Inv03
theorem e19InvAdjoin04 : (AdjoinRoot.mk f19 e19V04)*(AdjoinRoot.mk f19 e19I04)=1 := by exact e19InvAdjoin_of_poly e19Inv04
theorem e19InvAdjoin05 : (AdjoinRoot.mk f19 e19V05)*(AdjoinRoot.mk f19 e19I05)=1 := by exact e19InvAdjoin_of_poly e19Inv05
theorem e19InvAdjoin06 : (AdjoinRoot.mk f19 e19V06)*(AdjoinRoot.mk f19 e19I06)=1 := by exact e19InvAdjoin_of_poly e19Inv06
theorem e19InvAdjoin07 : (AdjoinRoot.mk f19 e19V07)*(AdjoinRoot.mk f19 e19I07)=1 := by exact e19InvAdjoin_of_poly e19Inv07
theorem e19InvAdjoin08 : (AdjoinRoot.mk f19 e19V08)*(AdjoinRoot.mk f19 e19I08)=1 := by exact e19InvAdjoin_of_poly e19Inv08
theorem e19InvAdjoin09 : (AdjoinRoot.mk f19 e19V09)*(AdjoinRoot.mk f19 e19I09)=1 := by exact e19InvAdjoin_of_poly e19Inv09
theorem e19InvAdjoin10 : (AdjoinRoot.mk f19 e19V10)*(AdjoinRoot.mk f19 e19I10)=1 := by exact e19InvAdjoin_of_poly e19Inv10
theorem e19InvAdjoin19 : (AdjoinRoot.mk f19 e19V11)*(AdjoinRoot.mk f19 e19I11)=1 := by exact e19InvAdjoin_of_poly e19Inv11
theorem e19InvAdjoin12 : (AdjoinRoot.mk f19 e19V12)*(AdjoinRoot.mk f19 e19I12)=1 := by exact e19InvAdjoin_of_poly e19Inv12
theorem e19InvAdjoin13 : (AdjoinRoot.mk f19 e19V13)*(AdjoinRoot.mk f19 e19I13)=1 := by exact e19InvAdjoin_of_poly e19Inv13
theorem e19InvAdjoin14 : (AdjoinRoot.mk f19 e19V14)*(AdjoinRoot.mk f19 e19I14)=1 := by exact e19InvAdjoin_of_poly e19Inv14
theorem e19InvAdjoin15 : (AdjoinRoot.mk f19 e19V15)*(AdjoinRoot.mk f19 e19I15)=1 := by exact e19InvAdjoin_of_poly e19Inv15
theorem e19InverseSumAdjoin : AdjoinRoot.mk f19 e19I01 + AdjoinRoot.mk f19 e19I02 + AdjoinRoot.mk f19 e19I03 + AdjoinRoot.mk f19 e19I04 + AdjoinRoot.mk f19 e19I05 + AdjoinRoot.mk f19 e19I06 + AdjoinRoot.mk f19 e19I07 + AdjoinRoot.mk f19 e19I08 + AdjoinRoot.mk f19 e19I09 + AdjoinRoot.mk f19 e19I10 + AdjoinRoot.mk f19 e19I11 + AdjoinRoot.mk f19 e19I12 + AdjoinRoot.mk f19 e19I13 + AdjoinRoot.mk f19 e19I14 + AdjoinRoot.mk f19 e19I15 = 0 := by
  have h := congrArg (AdjoinRoot.mk f19) e19InverseSum
  simpa only [map_add,map_zero] using h
#print axioms e19InvAdjoin01
#print axioms e19InverseSumAdjoin
