import Carlet.N11FourInverseProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
local instance : CharP (AdjoinRoot f) 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f)).injective 2
theorem e11InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f*q) : (AdjoinRoot.mk f v)*(AdjoinRoot.mk f i)=1 := by
  have hd : f ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f v)*(AdjoinRoot.mk f i)+1=0 := by simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f v)*(AdjoinRoot.mk f i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f)+1=0 := by
        calc
          (1:AdjoinRoot f)+1=(2:AdjoinRoot f) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f) 2
      exact neg_eq_of_add_eq_zero_left ht
theorem e11InvAdjoin01 : (AdjoinRoot.mk f e11V01)*(AdjoinRoot.mk f e11I01)=1 := by exact e11InvAdjoin_of_poly e11Inv01
theorem e11InvAdjoin02 : (AdjoinRoot.mk f e11V02)*(AdjoinRoot.mk f e11I02)=1 := by exact e11InvAdjoin_of_poly e11Inv02
theorem e11InvAdjoin03 : (AdjoinRoot.mk f e11V03)*(AdjoinRoot.mk f e11I03)=1 := by exact e11InvAdjoin_of_poly e11Inv03
theorem e11InvAdjoin04 : (AdjoinRoot.mk f e11V04)*(AdjoinRoot.mk f e11I04)=1 := by exact e11InvAdjoin_of_poly e11Inv04
theorem e11InvAdjoin05 : (AdjoinRoot.mk f e11V05)*(AdjoinRoot.mk f e11I05)=1 := by exact e11InvAdjoin_of_poly e11Inv05
theorem e11InvAdjoin06 : (AdjoinRoot.mk f e11V06)*(AdjoinRoot.mk f e11I06)=1 := by exact e11InvAdjoin_of_poly e11Inv06
theorem e11InvAdjoin07 : (AdjoinRoot.mk f e11V07)*(AdjoinRoot.mk f e11I07)=1 := by exact e11InvAdjoin_of_poly e11Inv07
theorem e11InvAdjoin08 : (AdjoinRoot.mk f e11V08)*(AdjoinRoot.mk f e11I08)=1 := by exact e11InvAdjoin_of_poly e11Inv08
theorem e11InvAdjoin09 : (AdjoinRoot.mk f e11V09)*(AdjoinRoot.mk f e11I09)=1 := by exact e11InvAdjoin_of_poly e11Inv09
theorem e11InvAdjoin10 : (AdjoinRoot.mk f e11V10)*(AdjoinRoot.mk f e11I10)=1 := by exact e11InvAdjoin_of_poly e11Inv10
theorem e11InvAdjoin11 : (AdjoinRoot.mk f e11V11)*(AdjoinRoot.mk f e11I11)=1 := by exact e11InvAdjoin_of_poly e11Inv11
theorem e11InvAdjoin12 : (AdjoinRoot.mk f e11V12)*(AdjoinRoot.mk f e11I12)=1 := by exact e11InvAdjoin_of_poly e11Inv12
theorem e11InvAdjoin13 : (AdjoinRoot.mk f e11V13)*(AdjoinRoot.mk f e11I13)=1 := by exact e11InvAdjoin_of_poly e11Inv13
theorem e11InvAdjoin14 : (AdjoinRoot.mk f e11V14)*(AdjoinRoot.mk f e11I14)=1 := by exact e11InvAdjoin_of_poly e11Inv14
theorem e11InvAdjoin15 : (AdjoinRoot.mk f e11V15)*(AdjoinRoot.mk f e11I15)=1 := by exact e11InvAdjoin_of_poly e11Inv15
theorem e11InverseSumAdjoin : AdjoinRoot.mk f e11I01 + AdjoinRoot.mk f e11I02 + AdjoinRoot.mk f e11I03 + AdjoinRoot.mk f e11I04 + AdjoinRoot.mk f e11I05 + AdjoinRoot.mk f e11I06 + AdjoinRoot.mk f e11I07 + AdjoinRoot.mk f e11I08 + AdjoinRoot.mk f e11I09 + AdjoinRoot.mk f e11I10 + AdjoinRoot.mk f e11I11 + AdjoinRoot.mk f e11I12 + AdjoinRoot.mk f e11I13 + AdjoinRoot.mk f e11I14 + AdjoinRoot.mk f e11I15 = 0 := by
  have h := congrArg (AdjoinRoot.mk f) e11InverseSum
  simpa only [map_add,map_zero] using h
#print axioms e11InvAdjoin01
#print axioms e11InverseSumAdjoin
