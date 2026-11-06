import Carlet.N9InverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
local instance : CharP (AdjoinRoot f9) 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f9)).injective 2
theorem d9InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f9*q) : (AdjoinRoot.mk f9 v)*(AdjoinRoot.mk f9 i)=1 := by
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
theorem d9InvAdjoin01 : (AdjoinRoot.mk f9 d9V01)*(AdjoinRoot.mk f9 d9I01)=1 := by exact d9InvAdjoin_of_poly d9Inv01
theorem d9InvAdjoin02 : (AdjoinRoot.mk f9 d9V02)*(AdjoinRoot.mk f9 d9I02)=1 := by exact d9InvAdjoin_of_poly d9Inv02
theorem d9InvAdjoin03 : (AdjoinRoot.mk f9 d9V03)*(AdjoinRoot.mk f9 d9I03)=1 := by exact d9InvAdjoin_of_poly d9Inv03
theorem d9InvAdjoin04 : (AdjoinRoot.mk f9 d9V04)*(AdjoinRoot.mk f9 d9I04)=1 := by exact d9InvAdjoin_of_poly d9Inv04
theorem d9InvAdjoin05 : (AdjoinRoot.mk f9 d9V05)*(AdjoinRoot.mk f9 d9I05)=1 := by exact d9InvAdjoin_of_poly d9Inv05
theorem d9InvAdjoin06 : (AdjoinRoot.mk f9 d9V06)*(AdjoinRoot.mk f9 d9I06)=1 := by exact d9InvAdjoin_of_poly d9Inv06
theorem d9InvAdjoin07 : (AdjoinRoot.mk f9 d9V07)*(AdjoinRoot.mk f9 d9I07)=1 := by exact d9InvAdjoin_of_poly d9Inv07
theorem d9InvAdjoin08 : (AdjoinRoot.mk f9 d9V08)*(AdjoinRoot.mk f9 d9I08)=1 := by exact d9InvAdjoin_of_poly d9Inv08
theorem d9InvAdjoin09 : (AdjoinRoot.mk f9 d9V09)*(AdjoinRoot.mk f9 d9I09)=1 := by exact d9InvAdjoin_of_poly d9Inv09
theorem d9InvAdjoin10 : (AdjoinRoot.mk f9 d9V10)*(AdjoinRoot.mk f9 d9I10)=1 := by exact d9InvAdjoin_of_poly d9Inv10
theorem d9InvAdjoin11 : (AdjoinRoot.mk f9 d9V11)*(AdjoinRoot.mk f9 d9I11)=1 := by exact d9InvAdjoin_of_poly d9Inv11
theorem d9InvAdjoin12 : (AdjoinRoot.mk f9 d9V12)*(AdjoinRoot.mk f9 d9I12)=1 := by exact d9InvAdjoin_of_poly d9Inv12
theorem d9InvAdjoin13 : (AdjoinRoot.mk f9 d9V13)*(AdjoinRoot.mk f9 d9I13)=1 := by exact d9InvAdjoin_of_poly d9Inv13
theorem d9InvAdjoin14 : (AdjoinRoot.mk f9 d9V14)*(AdjoinRoot.mk f9 d9I14)=1 := by exact d9InvAdjoin_of_poly d9Inv14
theorem d9InvAdjoin15 : (AdjoinRoot.mk f9 d9V15)*(AdjoinRoot.mk f9 d9I15)=1 := by exact d9InvAdjoin_of_poly d9Inv15
theorem d9InverseSumAdjoin : AdjoinRoot.mk f9 d9I01 + AdjoinRoot.mk f9 d9I02 + AdjoinRoot.mk f9 d9I03 + AdjoinRoot.mk f9 d9I04 + AdjoinRoot.mk f9 d9I05 + AdjoinRoot.mk f9 d9I06 + AdjoinRoot.mk f9 d9I07 + AdjoinRoot.mk f9 d9I08 + AdjoinRoot.mk f9 d9I09 + AdjoinRoot.mk f9 d9I10 + AdjoinRoot.mk f9 d9I11 + AdjoinRoot.mk f9 d9I12 + AdjoinRoot.mk f9 d9I13 + AdjoinRoot.mk f9 d9I14 + AdjoinRoot.mk f9 d9I15 = 0 := by
  have h := congrArg (AdjoinRoot.mk f9) d9InverseSum
  simpa only [map_add,map_zero] using h
#print axioms d9InvAdjoin01
#print axioms d9InverseSumAdjoin
