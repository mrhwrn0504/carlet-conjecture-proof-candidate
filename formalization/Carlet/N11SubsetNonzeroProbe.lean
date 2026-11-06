import Carlet.N11SubsetSumProbe
import Mathlib.Tactic
noncomputable section
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
lemma mul_eq_one_left_ne_zero {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a*b=1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h
theorem certV01_nonzero : AdjoinRoot.mk f certV01 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin01
theorem certSubsetSum01_nonzero : (∑ j ∈ ({0} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum01]
  exact certV01_nonzero
theorem certV02_nonzero : AdjoinRoot.mk f certV02 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin02
theorem certSubsetSum02_nonzero : (∑ j ∈ ({1} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum02]
  exact certV02_nonzero
theorem certV03_nonzero : AdjoinRoot.mk f certV03 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin03
theorem certSubsetSum03_nonzero : (∑ j ∈ ({0,1} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum03]
  exact certV03_nonzero
theorem certV04_nonzero : AdjoinRoot.mk f certV04 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin04
theorem certSubsetSum04_nonzero : (∑ j ∈ ({2} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum04]
  exact certV04_nonzero
theorem certV05_nonzero : AdjoinRoot.mk f certV05 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin05
theorem certSubsetSum05_nonzero : (∑ j ∈ ({0,2} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum05]
  exact certV05_nonzero
theorem certV06_nonzero : AdjoinRoot.mk f certV06 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin06
theorem certSubsetSum06_nonzero : (∑ j ∈ ({1,2} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum06]
  exact certV06_nonzero
theorem certV07_nonzero : AdjoinRoot.mk f certV07 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin07
theorem certSubsetSum07_nonzero : (∑ j ∈ ({0,1,2} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum07]
  exact certV07_nonzero
theorem certV08_nonzero : AdjoinRoot.mk f certV08 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin08
theorem certSubsetSum08_nonzero : (∑ j ∈ ({3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum08]
  exact certV08_nonzero
theorem certV09_nonzero : AdjoinRoot.mk f certV09 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin09
theorem certSubsetSum09_nonzero : (∑ j ∈ ({0,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum09]
  exact certV09_nonzero
theorem certV10_nonzero : AdjoinRoot.mk f certV10 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin10
theorem certSubsetSum10_nonzero : (∑ j ∈ ({1,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum10]
  exact certV10_nonzero
theorem certV11_nonzero : AdjoinRoot.mk f certV11 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin11
theorem certSubsetSum11_nonzero : (∑ j ∈ ({0,1,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum11]
  exact certV11_nonzero
theorem certV12_nonzero : AdjoinRoot.mk f certV12 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin12
theorem certSubsetSum12_nonzero : (∑ j ∈ ({2,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum12]
  exact certV12_nonzero
theorem certV13_nonzero : AdjoinRoot.mk f certV13 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin13
theorem certSubsetSum13_nonzero : (∑ j ∈ ({0,2,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum13]
  exact certV13_nonzero
theorem certV14_nonzero : AdjoinRoot.mk f certV14 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin14
theorem certSubsetSum14_nonzero : (∑ j ∈ ({1,2,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum14]
  exact certV14_nonzero
theorem certV15_nonzero : AdjoinRoot.mk f certV15 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin15
theorem certSubsetSum15_nonzero : (∑ j ∈ ({0,1,2,3} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum15]
  exact certV15_nonzero
theorem certV16_nonzero : AdjoinRoot.mk f certV16 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin16
theorem certSubsetSum16_nonzero : (∑ j ∈ ({4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum16]
  exact certV16_nonzero
theorem certV17_nonzero : AdjoinRoot.mk f certV17 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin17
theorem certSubsetSum17_nonzero : (∑ j ∈ ({0,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum17]
  exact certV17_nonzero
theorem certV18_nonzero : AdjoinRoot.mk f certV18 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin18
theorem certSubsetSum18_nonzero : (∑ j ∈ ({1,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum18]
  exact certV18_nonzero
theorem certV19_nonzero : AdjoinRoot.mk f certV19 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin19
theorem certSubsetSum19_nonzero : (∑ j ∈ ({0,1,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum19]
  exact certV19_nonzero
theorem certV20_nonzero : AdjoinRoot.mk f certV20 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin20
theorem certSubsetSum20_nonzero : (∑ j ∈ ({2,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum20]
  exact certV20_nonzero
theorem certV21_nonzero : AdjoinRoot.mk f certV21 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin21
theorem certSubsetSum21_nonzero : (∑ j ∈ ({0,2,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum21]
  exact certV21_nonzero
theorem certV22_nonzero : AdjoinRoot.mk f certV22 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin22
theorem certSubsetSum22_nonzero : (∑ j ∈ ({1,2,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum22]
  exact certV22_nonzero
theorem certV23_nonzero : AdjoinRoot.mk f certV23 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin23
theorem certSubsetSum23_nonzero : (∑ j ∈ ({0,1,2,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum23]
  exact certV23_nonzero
theorem certV24_nonzero : AdjoinRoot.mk f certV24 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin24
theorem certSubsetSum24_nonzero : (∑ j ∈ ({3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum24]
  exact certV24_nonzero
theorem certV25_nonzero : AdjoinRoot.mk f certV25 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin25
theorem certSubsetSum25_nonzero : (∑ j ∈ ({0,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum25]
  exact certV25_nonzero
theorem certV26_nonzero : AdjoinRoot.mk f certV26 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin26
theorem certSubsetSum26_nonzero : (∑ j ∈ ({1,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum26]
  exact certV26_nonzero
theorem certV27_nonzero : AdjoinRoot.mk f certV27 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin27
theorem certSubsetSum27_nonzero : (∑ j ∈ ({0,1,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum27]
  exact certV27_nonzero
theorem certV28_nonzero : AdjoinRoot.mk f certV28 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin28
theorem certSubsetSum28_nonzero : (∑ j ∈ ({2,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum28]
  exact certV28_nonzero
theorem certV29_nonzero : AdjoinRoot.mk f certV29 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin29
theorem certSubsetSum29_nonzero : (∑ j ∈ ({0,2,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum29]
  exact certV29_nonzero
theorem certV30_nonzero : AdjoinRoot.mk f certV30 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin30
theorem certSubsetSum30_nonzero : (∑ j ∈ ({1,2,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum30]
  exact certV30_nonzero
theorem certV31_nonzero : AdjoinRoot.mk f certV31 ≠ 0 := mul_eq_one_left_ne_zero certInvAdjoin31
theorem certSubsetSum31_nonzero : (∑ j ∈ ({0,1,2,3,4} : Finset (Fin 5)), certBase j) ≠ 0 := by
  rw [certSubsetSum31]
  exact certV31_nonzero
#print axioms certSubsetSum01_nonzero
#print axioms certSubsetSum02_nonzero
#print axioms certSubsetSum03_nonzero
#print axioms certSubsetSum04_nonzero
#print axioms certSubsetSum05_nonzero
#print axioms certSubsetSum06_nonzero
#print axioms certSubsetSum07_nonzero
#print axioms certSubsetSum08_nonzero
#print axioms certSubsetSum09_nonzero
#print axioms certSubsetSum10_nonzero
#print axioms certSubsetSum11_nonzero
#print axioms certSubsetSum12_nonzero
#print axioms certSubsetSum13_nonzero
#print axioms certSubsetSum14_nonzero
#print axioms certSubsetSum15_nonzero
#print axioms certSubsetSum16_nonzero
#print axioms certSubsetSum17_nonzero
#print axioms certSubsetSum18_nonzero
#print axioms certSubsetSum19_nonzero
#print axioms certSubsetSum20_nonzero
#print axioms certSubsetSum21_nonzero
#print axioms certSubsetSum22_nonzero
#print axioms certSubsetSum23_nonzero
#print axioms certSubsetSum24_nonzero
#print axioms certSubsetSum25_nonzero
#print axioms certSubsetSum26_nonzero
#print axioms certSubsetSum27_nonzero
#print axioms certSubsetSum28_nonzero
#print axioms certSubsetSum29_nonzero
#print axioms certSubsetSum30_nonzero
#print axioms certSubsetSum31_nonzero



