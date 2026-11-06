import Carlet.N29FourASCertificateProbe
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial
noncomputable section
set_option linter.unnecessarySeqFocus false
local instance : Fact (Irreducible f29) := ⟨f29_irreducible⟩
local instance : CharP (AdjoinRoot f29) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f29)).injective 2

theorem n29K5InvAdjoin_of_poly {v i q : P17} (h : v*i+1=f29*q) :
    (AdjoinRoot.mk f29 v)*(AdjoinRoot.mk f29 i)=1 := by
  have hd : f29 ∣ v*i+1 := ⟨q,h⟩
  have hz : AdjoinRoot.mk f29 (v*i+1)=0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f29 v)*(AdjoinRoot.mk f29 i)+1=0 := by
    simpa only [map_add,map_mul,map_one] using hz
  calc
    (AdjoinRoot.mk f29 v)*(AdjoinRoot.mk f29 i) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1:AdjoinRoot f29)+1=0 := by
        calc
          (1:AdjoinRoot f29)+1=(2:AdjoinRoot f29) := by norm_num
          _=0 := CharP.cast_eq_zero (AdjoinRoot f29) 2
      exact neg_eq_of_add_eq_zero_left ht


#print axioms n29K5InvAdjoin_of_poly

