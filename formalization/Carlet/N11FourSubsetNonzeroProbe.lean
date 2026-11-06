import Carlet.N11FourSubsetSumProbe
import Carlet.N11FourInverseAdjoinProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
lemma mul_eq_one_left_ne_zero11Four {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem e11V01_nonzero : AdjoinRoot.mk f e11V01 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin01
theorem e11SubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum01]
  exact e11V01_nonzero
theorem e11V02_nonzero : AdjoinRoot.mk f e11V02 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin02
theorem e11SubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum02]
  exact e11V02_nonzero
theorem e11V03_nonzero : AdjoinRoot.mk f e11V03 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin03
theorem e11SubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum03]
  exact e11V03_nonzero
theorem e11V04_nonzero : AdjoinRoot.mk f e11V04 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin04
theorem e11SubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum04]
  exact e11V04_nonzero
theorem e11V05_nonzero : AdjoinRoot.mk f e11V05 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin05
theorem e11SubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum05]
  exact e11V05_nonzero
theorem e11V06_nonzero : AdjoinRoot.mk f e11V06 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin06
theorem e11SubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum06]
  exact e11V06_nonzero
theorem e11V07_nonzero : AdjoinRoot.mk f e11V07 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin07
theorem e11SubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum07]
  exact e11V07_nonzero
theorem e11V08_nonzero : AdjoinRoot.mk f e11V08 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin08
theorem e11SubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum08]
  exact e11V08_nonzero
theorem e11V09_nonzero : AdjoinRoot.mk f e11V09 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin09
theorem e11SubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum09]
  exact e11V09_nonzero
theorem e11V10_nonzero : AdjoinRoot.mk f e11V10 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin10
theorem e11SubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum10]
  exact e11V10_nonzero
theorem e11V11_nonzero : AdjoinRoot.mk f e11V11 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin11
theorem e11SubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum11]
  exact e11V11_nonzero
theorem e11V12_nonzero : AdjoinRoot.mk f e11V12 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin12
theorem e11SubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum12]
  exact e11V12_nonzero
theorem e11V13_nonzero : AdjoinRoot.mk f e11V13 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin13
theorem e11SubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum13]
  exact e11V13_nonzero
theorem e11V14_nonzero : AdjoinRoot.mk f e11V14 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin14
theorem e11SubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum14]
  exact e11V14_nonzero
theorem e11V15_nonzero : AdjoinRoot.mk f e11V15 ≠ 0 := mul_eq_one_left_ne_zero11Four e11InvAdjoin15
theorem e11SubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 4)), e11Base j) ≠ 0 := by
  rw [e11SubsetSum15]
  exact e11V15_nonzero

#print axioms e11SubsetSum01_nonzero
#print axioms e11SubsetSum15_nonzero
