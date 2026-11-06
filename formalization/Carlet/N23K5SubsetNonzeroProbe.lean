import Carlet.N23K5SubsetSumProbe
import Carlet.N23K5InverseAdjoinProbe
import Mathlib.Tactic
set_option linter.unnecessarySeqFocus false
noncomputable section
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩
lemma n23K5_mul_eq_one_left_ne_zero {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem n23K5V01_nonzero : AdjoinRoot.mk f23 n23K5V01 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin01
theorem n23K5SubsetSum01_nonzero : (∑ i ∈ ({0} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum01]
  exact n23K5V01_nonzero
theorem n23K5V02_nonzero : AdjoinRoot.mk f23 n23K5V02 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin02
theorem n23K5SubsetSum02_nonzero : (∑ i ∈ ({1} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum02]
  exact n23K5V02_nonzero
theorem n23K5V03_nonzero : AdjoinRoot.mk f23 n23K5V03 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin03
theorem n23K5SubsetSum03_nonzero : (∑ i ∈ ({0,1} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum03]
  exact n23K5V03_nonzero
theorem n23K5V04_nonzero : AdjoinRoot.mk f23 n23K5V04 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin04
theorem n23K5SubsetSum04_nonzero : (∑ i ∈ ({2} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum04]
  exact n23K5V04_nonzero
theorem n23K5V05_nonzero : AdjoinRoot.mk f23 n23K5V05 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin05
theorem n23K5SubsetSum05_nonzero : (∑ i ∈ ({0,2} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum05]
  exact n23K5V05_nonzero
theorem n23K5V06_nonzero : AdjoinRoot.mk f23 n23K5V06 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin06
theorem n23K5SubsetSum06_nonzero : (∑ i ∈ ({1,2} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum06]
  exact n23K5V06_nonzero
theorem n23K5V07_nonzero : AdjoinRoot.mk f23 n23K5V07 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin07
theorem n23K5SubsetSum07_nonzero : (∑ i ∈ ({0,1,2} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum07]
  exact n23K5V07_nonzero
theorem n23K5V08_nonzero : AdjoinRoot.mk f23 n23K5V08 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin08
theorem n23K5SubsetSum08_nonzero : (∑ i ∈ ({3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum08]
  exact n23K5V08_nonzero
theorem n23K5V09_nonzero : AdjoinRoot.mk f23 n23K5V09 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin09
theorem n23K5SubsetSum09_nonzero : (∑ i ∈ ({0,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum09]
  exact n23K5V09_nonzero
theorem n23K5V10_nonzero : AdjoinRoot.mk f23 n23K5V10 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin10
theorem n23K5SubsetSum10_nonzero : (∑ i ∈ ({1,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum10]
  exact n23K5V10_nonzero
theorem n23K5V11_nonzero : AdjoinRoot.mk f23 n23K5V11 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin11
theorem n23K5SubsetSum11_nonzero : (∑ i ∈ ({0,1,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum11]
  exact n23K5V11_nonzero
theorem n23K5V12_nonzero : AdjoinRoot.mk f23 n23K5V12 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin12
theorem n23K5SubsetSum12_nonzero : (∑ i ∈ ({2,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum12]
  exact n23K5V12_nonzero
theorem n23K5V13_nonzero : AdjoinRoot.mk f23 n23K5V13 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin13
theorem n23K5SubsetSum13_nonzero : (∑ i ∈ ({0,2,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum13]
  exact n23K5V13_nonzero
theorem n23K5V14_nonzero : AdjoinRoot.mk f23 n23K5V14 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin14
theorem n23K5SubsetSum14_nonzero : (∑ i ∈ ({1,2,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum14]
  exact n23K5V14_nonzero
theorem n23K5V15_nonzero : AdjoinRoot.mk f23 n23K5V15 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin15
theorem n23K5SubsetSum15_nonzero : (∑ i ∈ ({0,1,2,3} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum15]
  exact n23K5V15_nonzero
theorem n23K5V16_nonzero : AdjoinRoot.mk f23 n23K5V16 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin16
theorem n23K5SubsetSum16_nonzero : (∑ i ∈ ({4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum16]
  exact n23K5V16_nonzero
theorem n23K5V17_nonzero : AdjoinRoot.mk f23 n23K5V17 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin17
theorem n23K5SubsetSum17_nonzero : (∑ i ∈ ({0,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum17]
  exact n23K5V17_nonzero
theorem n23K5V18_nonzero : AdjoinRoot.mk f23 n23K5V18 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin18
theorem n23K5SubsetSum18_nonzero : (∑ i ∈ ({1,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum18]
  exact n23K5V18_nonzero
theorem n23K5V19_nonzero : AdjoinRoot.mk f23 n23K5V19 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin19
theorem n23K5SubsetSum19_nonzero : (∑ i ∈ ({0,1,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum19]
  exact n23K5V19_nonzero
theorem n23K5V20_nonzero : AdjoinRoot.mk f23 n23K5V20 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin20
theorem n23K5SubsetSum20_nonzero : (∑ i ∈ ({2,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum20]
  exact n23K5V20_nonzero
theorem n23K5V21_nonzero : AdjoinRoot.mk f23 n23K5V21 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin21
theorem n23K5SubsetSum21_nonzero : (∑ i ∈ ({0,2,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum21]
  exact n23K5V21_nonzero
theorem n23K5V22_nonzero : AdjoinRoot.mk f23 n23K5V22 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin22
theorem n23K5SubsetSum22_nonzero : (∑ i ∈ ({1,2,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum22]
  exact n23K5V22_nonzero
theorem n23K5V23_nonzero : AdjoinRoot.mk f23 n23K5V23 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin23
theorem n23K5SubsetSum23_nonzero : (∑ i ∈ ({0,1,2,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum23]
  exact n23K5V23_nonzero
theorem n23K5V24_nonzero : AdjoinRoot.mk f23 n23K5V24 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin24
theorem n23K5SubsetSum24_nonzero : (∑ i ∈ ({3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum24]
  exact n23K5V24_nonzero
theorem n23K5V25_nonzero : AdjoinRoot.mk f23 n23K5V25 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin25
theorem n23K5SubsetSum25_nonzero : (∑ i ∈ ({0,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum25]
  exact n23K5V25_nonzero
theorem n23K5V26_nonzero : AdjoinRoot.mk f23 n23K5V26 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin26
theorem n23K5SubsetSum26_nonzero : (∑ i ∈ ({1,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum26]
  exact n23K5V26_nonzero
theorem n23K5V27_nonzero : AdjoinRoot.mk f23 n23K5V27 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin27
theorem n23K5SubsetSum27_nonzero : (∑ i ∈ ({0,1,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum27]
  exact n23K5V27_nonzero
theorem n23K5V28_nonzero : AdjoinRoot.mk f23 n23K5V28 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin28
theorem n23K5SubsetSum28_nonzero : (∑ i ∈ ({2,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum28]
  exact n23K5V28_nonzero
theorem n23K5V29_nonzero : AdjoinRoot.mk f23 n23K5V29 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin29
theorem n23K5SubsetSum29_nonzero : (∑ i ∈ ({0,2,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum29]
  exact n23K5V29_nonzero
theorem n23K5V30_nonzero : AdjoinRoot.mk f23 n23K5V30 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin30
theorem n23K5SubsetSum30_nonzero : (∑ i ∈ ({1,2,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum30]
  exact n23K5V30_nonzero
theorem n23K5V31_nonzero : AdjoinRoot.mk f23 n23K5V31 ≠ 0 := n23K5_mul_eq_one_left_ne_zero n23K5InvAdjoin31
theorem n23K5SubsetSum31_nonzero : (∑ i ∈ ({0,1,2,3,4} : Finset (Fin 5)), n23K5Base i) ≠ 0 := by
  rw [n23K5SubsetSum31]
  exact n23K5V31_nonzero
#print axioms n23K5SubsetSum01_nonzero
#print axioms n23K5SubsetSum31_nonzero
