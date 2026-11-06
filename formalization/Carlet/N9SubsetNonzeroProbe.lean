import Carlet.N9SubsetSumProbe
import Carlet.N9InverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f9) := ⟨f9_irreducible⟩
lemma mul_eq_one_left_ne_zero9 {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem d9V01_nonzero : AdjoinRoot.mk f9 d9V01 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin01
theorem d9SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum01]
  exact d9V01_nonzero
theorem d9V02_nonzero : AdjoinRoot.mk f9 d9V02 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin02
theorem d9SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum02]
  exact d9V02_nonzero
theorem d9V03_nonzero : AdjoinRoot.mk f9 d9V03 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin03
theorem d9SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum03]
  exact d9V03_nonzero
theorem d9V04_nonzero : AdjoinRoot.mk f9 d9V04 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin04
theorem d9SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum04]
  exact d9V04_nonzero
theorem d9V05_nonzero : AdjoinRoot.mk f9 d9V05 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin05
theorem d9SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum05]
  exact d9V05_nonzero
theorem d9V06_nonzero : AdjoinRoot.mk f9 d9V06 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin06
theorem d9SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum06]
  exact d9V06_nonzero
theorem d9V07_nonzero : AdjoinRoot.mk f9 d9V07 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin07
theorem d9SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum07]
  exact d9V07_nonzero
theorem d9V08_nonzero : AdjoinRoot.mk f9 d9V08 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin08
theorem d9SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum08]
  exact d9V08_nonzero
theorem d9V09_nonzero : AdjoinRoot.mk f9 d9V09 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin09
theorem d9SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum09]
  exact d9V09_nonzero
theorem d9V10_nonzero : AdjoinRoot.mk f9 d9V10 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin10
theorem d9SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum10]
  exact d9V10_nonzero
theorem d9V11_nonzero : AdjoinRoot.mk f9 d9V11 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin11
theorem d9SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum11]
  exact d9V11_nonzero
theorem d9V12_nonzero : AdjoinRoot.mk f9 d9V12 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin12
theorem d9SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum12]
  exact d9V12_nonzero
theorem d9V13_nonzero : AdjoinRoot.mk f9 d9V13 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin13
theorem d9SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum13]
  exact d9V13_nonzero
theorem d9V14_nonzero : AdjoinRoot.mk f9 d9V14 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin14
theorem d9SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum14]
  exact d9V14_nonzero
theorem d9V15_nonzero : AdjoinRoot.mk f9 d9V15 ≠ 0 := mul_eq_one_left_ne_zero9 d9InvAdjoin15
theorem d9SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 4)), d9Base j) ≠ 0 := by
  rw [d9SubsetSum15]
  exact d9V15_nonzero

#print axioms d9SubsetSum01_nonzero
#print axioms d9SubsetSum15_nonzero
