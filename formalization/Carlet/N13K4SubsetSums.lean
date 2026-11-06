import Carlet.N13K4GeneratedData
import Mathlib.Tactic
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
local instance : Fact (Irreducible f13) := ⟨f13_irreducible⟩
namespace N13K4
def base (i : Fin 4) : AdjoinRoot f13 := AdjoinRoot.mk f13 (Carlet.n13K4BasePoly i)

theorem subsetSum01 : (∑ i ∈ ({0} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P01 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P01 := by
      have hp : (∑ i ∈ ({0} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P01 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P01] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum02 : (∑ i ∈ ({1} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P02 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P02 := by
      have hp : (∑ i ∈ ({1} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P02 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P02] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum03 : (∑ i ∈ ({0,1} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P03 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P03 := by
      have hp : (∑ i ∈ ({0,1} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P03 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P03] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum04 : (∑ i ∈ ({2} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P04 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P04 := by
      have hp : (∑ i ∈ ({2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P04 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P04] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum05 : (∑ i ∈ ({0,2} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P05 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P05 := by
      have hp : (∑ i ∈ ({0,2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P05 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P05] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum06 : (∑ i ∈ ({1,2} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P06 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P06 := by
      have hp : (∑ i ∈ ({1,2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P06 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P06] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum07 : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P07 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P07 := by
      have hp : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P07 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P07] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum08 : (∑ i ∈ ({3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P08 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P08 := by
      have hp : (∑ i ∈ ({3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P08 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P08] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum09 : (∑ i ∈ ({0,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P09 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P09 := by
      have hp : (∑ i ∈ ({0,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P09 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P09] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum10 : (∑ i ∈ ({1,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P10 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P10 := by
      have hp : (∑ i ∈ ({1,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P10 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P10] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum11 : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P11 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P11 := by
      have hp : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P11 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P11] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum12 : (∑ i ∈ ({2,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P12 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P12 := by
      have hp : (∑ i ∈ ({2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P12 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P12] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum13 : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P13 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P13 := by
      have hp : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P13 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P13] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum14 : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P14 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({1,2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P14 := by
      have hp : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P14 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P14] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

theorem subsetSum15 : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), base i) = AdjoinRoot.mk f13 Carlet.n13K4P15 := by
  classical
  calc
    _ = AdjoinRoot.mk f13 (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) := (map_sum (AdjoinRoot.mk f13) _ _).symm
    _ = AdjoinRoot.mk f13 Carlet.n13K4P15 := by
      have hp : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), Carlet.n13K4BasePoly i) = Carlet.n13K4P15 := by
        simp [Carlet.n13K4BasePoly, Carlet.n13K4Base0, Carlet.n13K4Base1, Carlet.n13K4Base2, Carlet.n13K4Base3, Carlet.n13K4P15] <;> ring_nf <;> simp [c2_13,c3_13,c4_13,c5_13,c6_13,c7_13,c8_13,c9_13,c10_13,c11_13,c12_13,c13_13,c14_13,c15_13,c16_13,c17_13,c18_13,c19_13,c20_13,c21_13,c22_13,c23_13,c24_13]
      exact congrArg (AdjoinRoot.mk f13) hp

#print axioms subsetSum01
#print axioms subsetSum15
end N13K4
namespace N13K4
theorem left_mul_ne_zero {R : Type*} [MonoidWithZero R] [Nontrivial R] {a b : R} (h : a * b = 1) : a ≠ 0 := by
  intro ha
  rw [ha, zero_mul] at h
  exact zero_ne_one h

theorem subsetSum01_ne_zero : (∑ i ∈ ({0} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum01]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin01

theorem subsetSum02_ne_zero : (∑ i ∈ ({1} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum02]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin02

theorem subsetSum03_ne_zero : (∑ i ∈ ({0,1} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum03]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin03

theorem subsetSum04_ne_zero : (∑ i ∈ ({2} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum04]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin04

theorem subsetSum05_ne_zero : (∑ i ∈ ({0,2} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum05]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin05

theorem subsetSum06_ne_zero : (∑ i ∈ ({1,2} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum06]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin06

theorem subsetSum07_ne_zero : (∑ i ∈ ({0,1,2} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum07]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin07

theorem subsetSum08_ne_zero : (∑ i ∈ ({3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum08]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin08

theorem subsetSum09_ne_zero : (∑ i ∈ ({0,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum09]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin09

theorem subsetSum10_ne_zero : (∑ i ∈ ({1,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum10]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin10

theorem subsetSum11_ne_zero : (∑ i ∈ ({0,1,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum11]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin11

theorem subsetSum12_ne_zero : (∑ i ∈ ({2,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum12]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin12

theorem subsetSum13_ne_zero : (∑ i ∈ ({0,2,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum13]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin13

theorem subsetSum14_ne_zero : (∑ i ∈ ({1,2,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum14]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin14

theorem subsetSum15_ne_zero : (∑ i ∈ ({0,1,2,3} : Finset (Fin 4)), base i) ≠ 0 := by
  rw [subsetSum15]
  exact left_mul_ne_zero Carlet.n13K4InvAdjoin15

theorem subsetSum_ne_zero (s : Finset (Fin 4)) (hs : s.Nonempty) : (∑ i ∈ s, base i) ≠ 0 := by
  classical
  fin_cases s
  case «0» => simp_all
  case «1» => simpa using subsetSum01_ne_zero
  case «2» => simpa using subsetSum02_ne_zero
  case «3» => simpa using subsetSum03_ne_zero
  case «4» => simpa using subsetSum04_ne_zero
  case «5» => simpa using subsetSum05_ne_zero
  case «6» => simpa using subsetSum06_ne_zero
  case «7» => simpa using subsetSum07_ne_zero
  case «8» => simpa using subsetSum08_ne_zero
  case «9» => simpa using subsetSum09_ne_zero
  case «10» => simpa using subsetSum10_ne_zero
  case «11» => simpa using subsetSum11_ne_zero
  case «12» => simpa using subsetSum12_ne_zero
  case «13» => simpa using subsetSum13_ne_zero
  case «14» => simpa using subsetSum14_ne_zero
  case «15» => simpa using subsetSum15_ne_zero
#print axioms subsetSum_ne_zero
def support (g : Fin 4 → F13) : Finset (Fin 4) := Finset.univ.filter (fun i => g i = 1)
lemma support_coeff (g : Fin 4 → F13) (i : Fin 4) : g i = if i ∈ support g then 1 else 0 := by
  classical
  by_cases hi : i ∈ support g
  · have hgi : g i = 1 := by simpa [support] using hi
    rw [if_pos hi]
    exact hgi
  · have hne : g i ≠ 1 := by simpa [support] using hi
    have hv : (g i).val = 0 ∨ (g i).val = 1 := by
      have hx := ZMod.val_lt (g i)
      omega
    have hzero : g i = 0 := by
      rcases hv with h0 | h1
      · apply ZMod.val_injective 2
        simpa [h0]
      · have hone : g i = 1 := by
          apply ZMod.val_injective 2
          rw [h1]
          exact ZMod.val_cast_of_lt (by norm_num : (1 : Nat) < 2)
        exact (hne hone).elim
    simp [hi, hzero]
lemma support_sum (g : Fin 4 → F13) :
    (∑ i : Fin 4, g i • base i) = ∑ i ∈ support g, base i := by
  classical
  simp_rw [support_coeff]
  have ht (i : Fin 4) : (if i ∈ support g then (1 : F13) else 0) • base i =
      if i ∈ support g then base i else 0 := by
    by_cases h : i ∈ support g <;> simp [h]
  simp_rw [ht]
  simp
theorem base_linearIndependent : LinearIndependent F13 base := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hi
  have hv : (g i).val = 0 ∨ (g i).val = 1 := by
    have hx := ZMod.val_lt (g i)
    omega
  have hgi : g i = 1 := by
    rcases hv with h0 | h1
    · have hzero : g i = 0 := by
        apply ZMod.val_injective 2
        simpa [h0]
      exact (hi hzero).elim
    · apply ZMod.val_injective 2
      rw [h1]
      exact ZMod.val_cast_of_lt (by norm_num : (1 : Nat) < 2)
  have hs : (support g).Nonempty := ⟨i, by simp [support, hgi]⟩
  have hz : (∑ j ∈ support g, base j) = 0 := by
    calc
      _ = ∑ j : Fin 4, g j • base j := (support_sum g).symm
      _ = 0 := hg
  exact (subsetSum_ne_zero (support g) hs) hz
def subspace : Submodule F13 (AdjoinRoot f13) := LinearMap.range (Fintype.linearCombination F13 base)
theorem subspace_finrank : Module.finrank F13 subspace = 4 := by
  have hi : Function.Injective (Fintype.linearCombination F13 base) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp base_linearIndependent
  calc
    Module.finrank F13 subspace = Module.finrank F13 (Fin 4 → F13) := LinearMap.finrank_range_of_inj hi
    _ = 4 := by rw [Module.finrank_fintype_fun_eq_card]; simp
#print axioms base_linearIndependent
#print axioms subspace_finrank

end N13K4
