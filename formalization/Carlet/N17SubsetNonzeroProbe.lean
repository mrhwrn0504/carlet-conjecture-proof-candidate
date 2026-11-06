import Carlet.N17SubsetSumProbe
import Carlet.N17InverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
lemma mul_eq_one_left_ne_zero17 {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem c17V01_nonzero : AdjoinRoot.mk f17 c17V01 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin01
theorem c17SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum01]
  exact c17V01_nonzero
theorem c17V02_nonzero : AdjoinRoot.mk f17 c17V02 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin02
theorem c17SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum02]
  exact c17V02_nonzero
theorem c17V03_nonzero : AdjoinRoot.mk f17 c17V03 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin03
theorem c17SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum03]
  exact c17V03_nonzero
theorem c17V04_nonzero : AdjoinRoot.mk f17 c17V04 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin04
theorem c17SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum04]
  exact c17V04_nonzero
theorem c17V05_nonzero : AdjoinRoot.mk f17 c17V05 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin05
theorem c17SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum05]
  exact c17V05_nonzero
theorem c17V06_nonzero : AdjoinRoot.mk f17 c17V06 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin06
theorem c17SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum06]
  exact c17V06_nonzero
theorem c17V07_nonzero : AdjoinRoot.mk f17 c17V07 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin07
theorem c17SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum07]
  exact c17V07_nonzero
theorem c17V08_nonzero : AdjoinRoot.mk f17 c17V08 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin08
theorem c17SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum08]
  exact c17V08_nonzero
theorem c17V09_nonzero : AdjoinRoot.mk f17 c17V09 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin09
theorem c17SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum09]
  exact c17V09_nonzero
theorem c17V10_nonzero : AdjoinRoot.mk f17 c17V10 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin10
theorem c17SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum10]
  exact c17V10_nonzero
theorem c17V11_nonzero : AdjoinRoot.mk f17 c17V11 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin11
theorem c17SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum11]
  exact c17V11_nonzero
theorem c17V12_nonzero : AdjoinRoot.mk f17 c17V12 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin12
theorem c17SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum12]
  exact c17V12_nonzero
theorem c17V13_nonzero : AdjoinRoot.mk f17 c17V13 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin13
theorem c17SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum13]
  exact c17V13_nonzero
theorem c17V14_nonzero : AdjoinRoot.mk f17 c17V14 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin14
theorem c17SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum14]
  exact c17V14_nonzero
theorem c17V15_nonzero : AdjoinRoot.mk f17 c17V15 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin15
theorem c17SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum15]
  exact c17V15_nonzero
theorem c17V16_nonzero : AdjoinRoot.mk f17 c17V16 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin16
theorem c17SubsetSum16_nonzero : (∑ j ∈ ({4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum16]
  exact c17V16_nonzero
theorem c17V17_nonzero : AdjoinRoot.mk f17 c17V17 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin17
theorem c17SubsetSum17_nonzero : (∑ j ∈ ({0,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum17]
  exact c17V17_nonzero
theorem c17V18_nonzero : AdjoinRoot.mk f17 c17V18 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin18
theorem c17SubsetSum18_nonzero : (∑ j ∈ ({1,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum18]
  exact c17V18_nonzero
theorem c17V19_nonzero : AdjoinRoot.mk f17 c17V19 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin19
theorem c17SubsetSum19_nonzero : (∑ j ∈ ({0,1,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum19]
  exact c17V19_nonzero
theorem c17V20_nonzero : AdjoinRoot.mk f17 c17V20 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin20
theorem c17SubsetSum20_nonzero : (∑ j ∈ ({2,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum20]
  exact c17V20_nonzero
theorem c17V21_nonzero : AdjoinRoot.mk f17 c17V21 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin21
theorem c17SubsetSum21_nonzero : (∑ j ∈ ({0,2,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum21]
  exact c17V21_nonzero
theorem c17V22_nonzero : AdjoinRoot.mk f17 c17V22 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin22
theorem c17SubsetSum22_nonzero : (∑ j ∈ ({1,2,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum22]
  exact c17V22_nonzero
theorem c17V23_nonzero : AdjoinRoot.mk f17 c17V23 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin23
theorem c17SubsetSum23_nonzero : (∑ j ∈ ({0,1,2,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum23]
  exact c17V23_nonzero
theorem c17V24_nonzero : AdjoinRoot.mk f17 c17V24 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin24
theorem c17SubsetSum24_nonzero : (∑ j ∈ ({3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum24]
  exact c17V24_nonzero
theorem c17V25_nonzero : AdjoinRoot.mk f17 c17V25 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin25
theorem c17SubsetSum25_nonzero : (∑ j ∈ ({0,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum25]
  exact c17V25_nonzero
theorem c17V26_nonzero : AdjoinRoot.mk f17 c17V26 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin26
theorem c17SubsetSum26_nonzero : (∑ j ∈ ({1,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum26]
  exact c17V26_nonzero
theorem c17V27_nonzero : AdjoinRoot.mk f17 c17V27 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin27
theorem c17SubsetSum27_nonzero : (∑ j ∈ ({0,1,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum27]
  exact c17V27_nonzero
theorem c17V28_nonzero : AdjoinRoot.mk f17 c17V28 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin28
theorem c17SubsetSum28_nonzero : (∑ j ∈ ({2,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum28]
  exact c17V28_nonzero
theorem c17V29_nonzero : AdjoinRoot.mk f17 c17V29 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin29
theorem c17SubsetSum29_nonzero : (∑ j ∈ ({0,2,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum29]
  exact c17V29_nonzero
theorem c17V30_nonzero : AdjoinRoot.mk f17 c17V30 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin30
theorem c17SubsetSum30_nonzero : (∑ j ∈ ({1,2,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum30]
  exact c17V30_nonzero
theorem c17V31_nonzero : AdjoinRoot.mk f17 c17V31 ≠ 0 := mul_eq_one_left_ne_zero17 c17InvAdjoin31
theorem c17SubsetSum31_nonzero : (∑ j ∈ ({0,1,2,3,4} : Finset (Fin 5)), c17Base j) ≠ 0 := by
  rw [c17SubsetSum31]
  exact c17V31_nonzero
#print axioms c17SubsetSum01_nonzero
#print axioms c17SubsetSum31_nonzero

