import Carlet.N13SubsetSumProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
lemma mul_eq_one_left_ne_zero13 {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem cert13V01_nonzero : AdjoinRoot.mk f13 cert13V01 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin01
theorem cert13SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum01]
  exact cert13V01_nonzero
theorem cert13V02_nonzero : AdjoinRoot.mk f13 cert13V02 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin02
theorem cert13SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum02]
  exact cert13V02_nonzero
theorem cert13V03_nonzero : AdjoinRoot.mk f13 cert13V03 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin03
theorem cert13SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum03]
  exact cert13V03_nonzero
theorem cert13V04_nonzero : AdjoinRoot.mk f13 cert13V04 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin04
theorem cert13SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum04]
  exact cert13V04_nonzero
theorem cert13V05_nonzero : AdjoinRoot.mk f13 cert13V05 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin05
theorem cert13SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum05]
  exact cert13V05_nonzero
theorem cert13V06_nonzero : AdjoinRoot.mk f13 cert13V06 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin06
theorem cert13SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum06]
  exact cert13V06_nonzero
theorem cert13V07_nonzero : AdjoinRoot.mk f13 cert13V07 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin07
theorem cert13SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum07]
  exact cert13V07_nonzero
theorem cert13V08_nonzero : AdjoinRoot.mk f13 cert13V08 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin08
theorem cert13SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum08]
  exact cert13V08_nonzero
theorem cert13V09_nonzero : AdjoinRoot.mk f13 cert13V09 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin09
theorem cert13SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum09]
  exact cert13V09_nonzero
theorem cert13V10_nonzero : AdjoinRoot.mk f13 cert13V10 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin10
theorem cert13SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum10]
  exact cert13V10_nonzero
theorem cert13V11_nonzero : AdjoinRoot.mk f13 cert13V11 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin11
theorem cert13SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum11]
  exact cert13V11_nonzero
theorem cert13V12_nonzero : AdjoinRoot.mk f13 cert13V12 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin12
theorem cert13SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum12]
  exact cert13V12_nonzero
theorem cert13V13_nonzero : AdjoinRoot.mk f13 cert13V13 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin13
theorem cert13SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum13]
  exact cert13V13_nonzero
theorem cert13V14_nonzero : AdjoinRoot.mk f13 cert13V14 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin14
theorem cert13SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum14]
  exact cert13V14_nonzero
theorem cert13V15_nonzero : AdjoinRoot.mk f13 cert13V15 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin15
theorem cert13SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum15]
  exact cert13V15_nonzero
theorem cert13V16_nonzero : AdjoinRoot.mk f13 cert13V16 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin16
theorem cert13SubsetSum16_nonzero : (∑ j ∈ ({4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum16]
  exact cert13V16_nonzero
theorem cert13V17_nonzero : AdjoinRoot.mk f13 cert13V17 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin17
theorem cert13SubsetSum17_nonzero : (∑ j ∈ ({0,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum17]
  exact cert13V17_nonzero
theorem cert13V18_nonzero : AdjoinRoot.mk f13 cert13V18 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin18
theorem cert13SubsetSum18_nonzero : (∑ j ∈ ({1,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum18]
  exact cert13V18_nonzero
theorem cert13V19_nonzero : AdjoinRoot.mk f13 cert13V19 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin19
theorem cert13SubsetSum19_nonzero : (∑ j ∈ ({0,1,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum19]
  exact cert13V19_nonzero
theorem cert13V20_nonzero : AdjoinRoot.mk f13 cert13V20 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin20
theorem cert13SubsetSum20_nonzero : (∑ j ∈ ({2,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum20]
  exact cert13V20_nonzero
theorem cert13V21_nonzero : AdjoinRoot.mk f13 cert13V21 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin21
theorem cert13SubsetSum21_nonzero : (∑ j ∈ ({0,2,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum21]
  exact cert13V21_nonzero
theorem cert13V22_nonzero : AdjoinRoot.mk f13 cert13V22 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin22
theorem cert13SubsetSum22_nonzero : (∑ j ∈ ({1,2,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum22]
  exact cert13V22_nonzero
theorem cert13V23_nonzero : AdjoinRoot.mk f13 cert13V23 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin23
theorem cert13SubsetSum23_nonzero : (∑ j ∈ ({0,1,2,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum23]
  exact cert13V23_nonzero
theorem cert13V24_nonzero : AdjoinRoot.mk f13 cert13V24 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin24
theorem cert13SubsetSum24_nonzero : (∑ j ∈ ({3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum24]
  exact cert13V24_nonzero
theorem cert13V25_nonzero : AdjoinRoot.mk f13 cert13V25 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin25
theorem cert13SubsetSum25_nonzero : (∑ j ∈ ({0,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum25]
  exact cert13V25_nonzero
theorem cert13V26_nonzero : AdjoinRoot.mk f13 cert13V26 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin26
theorem cert13SubsetSum26_nonzero : (∑ j ∈ ({1,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum26]
  exact cert13V26_nonzero
theorem cert13V27_nonzero : AdjoinRoot.mk f13 cert13V27 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin27
theorem cert13SubsetSum27_nonzero : (∑ j ∈ ({0,1,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum27]
  exact cert13V27_nonzero
theorem cert13V28_nonzero : AdjoinRoot.mk f13 cert13V28 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin28
theorem cert13SubsetSum28_nonzero : (∑ j ∈ ({2,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum28]
  exact cert13V28_nonzero
theorem cert13V29_nonzero : AdjoinRoot.mk f13 cert13V29 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin29
theorem cert13SubsetSum29_nonzero : (∑ j ∈ ({0,2,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum29]
  exact cert13V29_nonzero
theorem cert13V30_nonzero : AdjoinRoot.mk f13 cert13V30 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin30
theorem cert13SubsetSum30_nonzero : (∑ j ∈ ({1,2,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum30]
  exact cert13V30_nonzero
theorem cert13V31_nonzero : AdjoinRoot.mk f13 cert13V31 ≠ 0 := mul_eq_one_left_ne_zero13 cert13InvAdjoin31
theorem cert13SubsetSum31_nonzero : (∑ j ∈ ({0,1,2,3,4} : Finset (Fin 5)), cert13Base j) ≠ 0 := by
  rw [cert13SubsetSum31]
  exact cert13V31_nonzero
#print axioms cert13SubsetSum01_nonzero
#print axioms cert13SubsetSum31_nonzero

