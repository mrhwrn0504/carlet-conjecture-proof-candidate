import Carlet.N25FourASCertificateProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial
noncomputable section
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f25) := ⟨f25_irreducible⟩
local instance : CharP (AdjoinRoot f25) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f25)).injective 2

theorem n25K5InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f25*q) :
    (AdjoinRoot.mk f25 v)*(AdjoinRoot.mk f25 i)=1 := by
  have hd : f25 ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f25 (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f25 v)*(AdjoinRoot.mk f25 i)+1=0 := by
    simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f25 v)*(AdjoinRoot.mk f25 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f25)+1=0 := by
        calc
          (1:AdjoinRoot f25)+1=(2:AdjoinRoot f25) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f25) 2
      exact neg_eq_of_add_eq_zero_left ht


#print axioms n25K5InvAdjoin_of_poly
