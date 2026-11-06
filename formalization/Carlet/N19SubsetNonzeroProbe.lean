import Carlet.N19SubsetSumProbe
import Carlet.N19InverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
lemma mul_eq_one_left_ne_zero19 {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem c19V01_nonzero : AdjoinRoot.mk f19 c19V01 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin01
theorem c19SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum01]
  exact c19V01_nonzero
theorem c19V02_nonzero : AdjoinRoot.mk f19 c19V02 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin02
theorem c19SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum02]
  exact c19V02_nonzero
theorem c19V03_nonzero : AdjoinRoot.mk f19 c19V03 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin03
theorem c19SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum03]
  exact c19V03_nonzero
theorem c19V04_nonzero : AdjoinRoot.mk f19 c19V04 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin04
theorem c19SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum04]
  exact c19V04_nonzero
theorem c19V05_nonzero : AdjoinRoot.mk f19 c19V05 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin05
theorem c19SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum05]
  exact c19V05_nonzero
theorem c19V06_nonzero : AdjoinRoot.mk f19 c19V06 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin06
theorem c19SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum06]
  exact c19V06_nonzero
theorem c19V07_nonzero : AdjoinRoot.mk f19 c19V07 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin07
theorem c19SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum07]
  exact c19V07_nonzero
theorem c19V08_nonzero : AdjoinRoot.mk f19 c19V08 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin08
theorem c19SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum08]
  exact c19V08_nonzero
theorem c19V09_nonzero : AdjoinRoot.mk f19 c19V09 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin09
theorem c19SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum09]
  exact c19V09_nonzero
theorem c19V10_nonzero : AdjoinRoot.mk f19 c19V10 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin10
theorem c19SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum10]
  exact c19V10_nonzero
theorem c19V11_nonzero : AdjoinRoot.mk f19 c19V11 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin11
theorem c19SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum11]
  exact c19V11_nonzero
theorem c19V12_nonzero : AdjoinRoot.mk f19 c19V12 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin12
theorem c19SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum12]
  exact c19V12_nonzero
theorem c19V13_nonzero : AdjoinRoot.mk f19 c19V13 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin13
theorem c19SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum13]
  exact c19V13_nonzero
theorem c19V14_nonzero : AdjoinRoot.mk f19 c19V14 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin14
theorem c19SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum14]
  exact c19V14_nonzero
theorem c19V15_nonzero : AdjoinRoot.mk f19 c19V15 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin15
theorem c19SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum15]
  exact c19V15_nonzero
theorem c19V16_nonzero : AdjoinRoot.mk f19 c19V16 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin16
theorem c19SubsetSum16_nonzero : (∑ j ∈ ({4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum16]
  exact c19V16_nonzero
theorem c19V17_nonzero : AdjoinRoot.mk f19 c19V17 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin17
theorem c19SubsetSum17_nonzero : (∑ j ∈ ({0,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum17]
  exact c19V17_nonzero
theorem c19V18_nonzero : AdjoinRoot.mk f19 c19V18 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin18
theorem c19SubsetSum18_nonzero : (∑ j ∈ ({1,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum18]
  exact c19V18_nonzero
theorem c19V19_nonzero : AdjoinRoot.mk f19 c19V19 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin19
theorem c19SubsetSum19_nonzero : (∑ j ∈ ({0,1,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum19]
  exact c19V19_nonzero
theorem c19V20_nonzero : AdjoinRoot.mk f19 c19V20 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin20
theorem c19SubsetSum20_nonzero : (∑ j ∈ ({2,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum20]
  exact c19V20_nonzero
theorem c19V21_nonzero : AdjoinRoot.mk f19 c19V21 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin21
theorem c19SubsetSum21_nonzero : (∑ j ∈ ({0,2,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum21]
  exact c19V21_nonzero
theorem c19V22_nonzero : AdjoinRoot.mk f19 c19V22 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin22
theorem c19SubsetSum22_nonzero : (∑ j ∈ ({1,2,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum22]
  exact c19V22_nonzero
theorem c19V23_nonzero : AdjoinRoot.mk f19 c19V23 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin23
theorem c19SubsetSum23_nonzero : (∑ j ∈ ({0,1,2,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum23]
  exact c19V23_nonzero
theorem c19V24_nonzero : AdjoinRoot.mk f19 c19V24 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin24
theorem c19SubsetSum24_nonzero : (∑ j ∈ ({3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum24]
  exact c19V24_nonzero
theorem c19V25_nonzero : AdjoinRoot.mk f19 c19V25 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin25
theorem c19SubsetSum25_nonzero : (∑ j ∈ ({0,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum25]
  exact c19V25_nonzero
theorem c19V26_nonzero : AdjoinRoot.mk f19 c19V26 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin26
theorem c19SubsetSum26_nonzero : (∑ j ∈ ({1,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum26]
  exact c19V26_nonzero
theorem c19V27_nonzero : AdjoinRoot.mk f19 c19V27 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin27
theorem c19SubsetSum27_nonzero : (∑ j ∈ ({0,1,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum27]
  exact c19V27_nonzero
theorem c19V28_nonzero : AdjoinRoot.mk f19 c19V28 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin28
theorem c19SubsetSum28_nonzero : (∑ j ∈ ({2,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum28]
  exact c19V28_nonzero
theorem c19V29_nonzero : AdjoinRoot.mk f19 c19V29 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin29
theorem c19SubsetSum29_nonzero : (∑ j ∈ ({0,2,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum29]
  exact c19V29_nonzero
theorem c19V30_nonzero : AdjoinRoot.mk f19 c19V30 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin30
theorem c19SubsetSum30_nonzero : (∑ j ∈ ({1,2,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum30]
  exact c19V30_nonzero
theorem c19V31_nonzero : AdjoinRoot.mk f19 c19V31 ≠ 0 := mul_eq_one_left_ne_zero19 c19InvAdjoin31
theorem c19SubsetSum31_nonzero : (∑ j ∈ ({0,1,2,3,4} : Finset (Fin 5)), c19Base j) ≠ 0 := by
  rw [c19SubsetSum31]
  exact c19V31_nonzero
#print axioms c19SubsetSum01_nonzero
#print axioms c19SubsetSum31_nonzero

