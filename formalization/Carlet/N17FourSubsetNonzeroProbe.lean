import Carlet.N17FourSubsetSumProbe
import Carlet.N17FourInverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f17) := ⟨f17_irreducible⟩
lemma mul_eq_one_left_ne_zero17Four {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem e17V01_nonzero : AdjoinRoot.mk f17 e17V01 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin01
theorem e17SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum01]
  exact e17V01_nonzero
theorem e17V02_nonzero : AdjoinRoot.mk f17 e17V02 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin02
theorem e17SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum02]
  exact e17V02_nonzero
theorem e17V03_nonzero : AdjoinRoot.mk f17 e17V03 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin03
theorem e17SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum03]
  exact e17V03_nonzero
theorem e17V04_nonzero : AdjoinRoot.mk f17 e17V04 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin04
theorem e17SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum04]
  exact e17V04_nonzero
theorem e17V05_nonzero : AdjoinRoot.mk f17 e17V05 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin05
theorem e17SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum05]
  exact e17V05_nonzero
theorem e17V06_nonzero : AdjoinRoot.mk f17 e17V06 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin06
theorem e17SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum06]
  exact e17V06_nonzero
theorem e17V07_nonzero : AdjoinRoot.mk f17 e17V07 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin07
theorem e17SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum07]
  exact e17V07_nonzero
theorem e17V08_nonzero : AdjoinRoot.mk f17 e17V08 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin08
theorem e17SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum08]
  exact e17V08_nonzero
theorem e17V09_nonzero : AdjoinRoot.mk f17 e17V09 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin09
theorem e17SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum09]
  exact e17V09_nonzero
theorem e17V10_nonzero : AdjoinRoot.mk f17 e17V10 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin10
theorem e17SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum10]
  exact e17V10_nonzero
theorem e17V11_nonzero : AdjoinRoot.mk f17 e17V11 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin17
theorem e17SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum11]
  exact e17V11_nonzero
theorem e17V12_nonzero : AdjoinRoot.mk f17 e17V12 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin12
theorem e17SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum12]
  exact e17V12_nonzero
theorem e17V13_nonzero : AdjoinRoot.mk f17 e17V13 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin13
theorem e17SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum13]
  exact e17V13_nonzero
theorem e17V14_nonzero : AdjoinRoot.mk f17 e17V14 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin14
theorem e17SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum14]
  exact e17V14_nonzero
theorem e17V15_nonzero : AdjoinRoot.mk f17 e17V15 ≠ 0 := mul_eq_one_left_ne_zero17Four e17InvAdjoin15
theorem e17SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 4)), e17Base j) ≠ 0 := by
  rw [e17SubsetSum15]
  exact e17V15_nonzero

#print axioms e17SubsetSum01_nonzero
#print axioms e17SubsetSum15_nonzero
