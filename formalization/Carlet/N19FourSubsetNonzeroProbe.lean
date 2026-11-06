import Carlet.N19FourSubsetSumProbe
import Carlet.N19FourInverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f19) := ⟨f19_certificate_irreducible⟩
lemma mul_eq_one_left_ne_zero19Four {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem e19V01_nonzero : AdjoinRoot.mk f19 e19V01 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin01
theorem e19SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum01]
  exact e19V01_nonzero
theorem e19V02_nonzero : AdjoinRoot.mk f19 e19V02 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin02
theorem e19SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum02]
  exact e19V02_nonzero
theorem e19V03_nonzero : AdjoinRoot.mk f19 e19V03 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin03
theorem e19SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum03]
  exact e19V03_nonzero
theorem e19V04_nonzero : AdjoinRoot.mk f19 e19V04 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin04
theorem e19SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum04]
  exact e19V04_nonzero
theorem e19V05_nonzero : AdjoinRoot.mk f19 e19V05 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin05
theorem e19SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum05]
  exact e19V05_nonzero
theorem e19V06_nonzero : AdjoinRoot.mk f19 e19V06 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin06
theorem e19SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum06]
  exact e19V06_nonzero
theorem e19V07_nonzero : AdjoinRoot.mk f19 e19V07 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin07
theorem e19SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum07]
  exact e19V07_nonzero
theorem e19V08_nonzero : AdjoinRoot.mk f19 e19V08 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin08
theorem e19SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum08]
  exact e19V08_nonzero
theorem e19V09_nonzero : AdjoinRoot.mk f19 e19V09 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin09
theorem e19SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum09]
  exact e19V09_nonzero
theorem e19V10_nonzero : AdjoinRoot.mk f19 e19V10 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin10
theorem e19SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum10]
  exact e19V10_nonzero
theorem e19V11_nonzero : AdjoinRoot.mk f19 e19V11 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin19
theorem e19SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum11]
  exact e19V11_nonzero
theorem e19V12_nonzero : AdjoinRoot.mk f19 e19V12 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin12
theorem e19SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum12]
  exact e19V12_nonzero
theorem e19V13_nonzero : AdjoinRoot.mk f19 e19V13 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin13
theorem e19SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum13]
  exact e19V13_nonzero
theorem e19V14_nonzero : AdjoinRoot.mk f19 e19V14 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin14
theorem e19SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum14]
  exact e19V14_nonzero
theorem e19V15_nonzero : AdjoinRoot.mk f19 e19V15 ≠ 0 := mul_eq_one_left_ne_zero19Four e19InvAdjoin15
theorem e19SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 4)), e19Base j) ≠ 0 := by
  rw [e19SubsetSum15]
  exact e19V15_nonzero

#print axioms e19SubsetSum01_nonzero
#print axioms e19SubsetSum15_nonzero
