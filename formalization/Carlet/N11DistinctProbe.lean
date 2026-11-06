import Carlet.N11UniquenessProbe
import Mathlib.Tactic
noncomputable section
set_option linter.unusedSimpArgs false
lemma certV01_degree_lt_all : certV01.natDegree < 11 := by
  unfold certV01
  compute_degree!
lemma certV02_degree_lt_all : certV02.natDegree < 11 := by
  unfold certV02
  compute_degree!
lemma certV03_degree_lt_all : certV03.natDegree < 11 := by
  unfold certV03
  compute_degree!
lemma certV04_degree_lt_all : certV04.natDegree < 11 := by
  unfold certV04
  compute_degree!
lemma certV05_degree_lt_all : certV05.natDegree < 11 := by
  unfold certV05
  compute_degree!
lemma certV06_degree_lt_all : certV06.natDegree < 11 := by
  unfold certV06
  compute_degree!
lemma certV07_degree_lt_all : certV07.natDegree < 11 := by
  unfold certV07
  compute_degree!
lemma certV08_degree_lt_all : certV08.natDegree < 11 := by
  unfold certV08
  compute_degree!
lemma certV09_degree_lt_all : certV09.natDegree < 11 := by
  unfold certV09
  compute_degree!
lemma certV10_degree_lt_all : certV10.natDegree < 11 := by
  unfold certV10
  compute_degree!
lemma certV11_degree_lt_all : certV11.natDegree < 11 := by
  unfold certV11
  compute_degree!
lemma certV12_degree_lt_all : certV12.natDegree < 11 := by
  unfold certV12
  compute_degree!
lemma certV13_degree_lt_all : certV13.natDegree < 11 := by
  unfold certV13
  compute_degree!
lemma certV14_degree_lt_all : certV14.natDegree < 11 := by
  unfold certV14
  compute_degree!
lemma certV15_degree_lt_all : certV15.natDegree < 11 := by
  unfold certV15
  compute_degree!
lemma certV16_degree_lt_all : certV16.natDegree < 11 := by
  unfold certV16
  compute_degree!
lemma certV17_degree_lt_all : certV17.natDegree < 11 := by
  unfold certV17
  compute_degree!
lemma certV18_degree_lt_all : certV18.natDegree < 11 := by
  unfold certV18
  compute_degree!
lemma certV19_degree_lt_all : certV19.natDegree < 11 := by
  unfold certV19
  compute_degree!
lemma certV20_degree_lt_all : certV20.natDegree < 11 := by
  unfold certV20
  compute_degree!
lemma certV21_degree_lt_all : certV21.natDegree < 11 := by
  unfold certV21
  compute_degree!
lemma certV22_degree_lt_all : certV22.natDegree < 11 := by
  unfold certV22
  compute_degree!
lemma certV23_degree_lt_all : certV23.natDegree < 11 := by
  unfold certV23
  compute_degree!
lemma certV24_degree_lt_all : certV24.natDegree < 11 := by
  unfold certV24
  compute_degree!
lemma certV25_degree_lt_all : certV25.natDegree < 11 := by
  unfold certV25
  compute_degree!
lemma certV26_degree_lt_all : certV26.natDegree < 11 := by
  unfold certV26
  compute_degree!
lemma certV27_degree_lt_all : certV27.natDegree < 11 := by
  unfold certV27
  compute_degree!
lemma certV28_degree_lt_all : certV28.natDegree < 11 := by
  unfold certV28
  compute_degree!
lemma certV29_degree_lt_all : certV29.natDegree < 11 := by
  unfold certV29
  compute_degree!
lemma certV30_degree_lt_all : certV30.natDegree < 11 := by
  unfold certV30
  compute_degree!
lemma certV31_degree_lt_all : certV31.natDegree < 11 := by
  unfold certV31
  compute_degree!
theorem certV01_ne_02 : certV01 ≠ certV02 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV02, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_03 : certV01 ≠ certV03 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV01, certV03, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_04 : certV01 ≠ certV04 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV04, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_05 : certV01 ≠ certV05 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV05, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_06 : certV01 ≠ certV06 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV06, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_07 : certV01 ≠ certV07 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV07, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_08 : certV01 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV01, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_09 : certV01 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_10 : certV01 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV01, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_11 : certV01 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_12 : certV01 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_13 : certV01 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_14 : certV01 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_15 : certV01 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_16 : certV01 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV01, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_17 : certV01 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_18 : certV01 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV01, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_19 : certV01 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_20 : certV01 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_21 : certV01 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_22 : certV01 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_23 : certV01 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_24 : certV01 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_25 : certV01 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV01, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_26 : certV01 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_27 : certV01 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV01, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_28 : certV01 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_29 : certV01 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_30 : certV01 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV01, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV01_ne_31 : certV01 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV01, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_03 : certV02 ≠ certV03 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV03, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_04 : certV02 ≠ certV04 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV04, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_05 : certV02 ≠ certV05 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV05, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_06 : certV02 ≠ certV06 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV06, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_07 : certV02 ≠ certV07 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV07, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_08 : certV02 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_09 : certV02 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV02, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_10 : certV02 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_11 : certV02 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV02, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_12 : certV02 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_13 : certV02 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_14 : certV02 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_15 : certV02 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_16 : certV02 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_17 : certV02 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV02, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_18 : certV02 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_19 : certV02 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV02, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_20 : certV02 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_21 : certV02 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_22 : certV02 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_23 : certV02 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_24 : certV02 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV02, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_25 : certV02 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_26 : certV02 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV02, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_27 : certV02 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_28 : certV02 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_29 : certV02 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_30 : certV02 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV02, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV02_ne_31 : certV02 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV02, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_04 : certV03 ≠ certV04 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV04, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_05 : certV03 ≠ certV05 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV05, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_06 : certV03 ≠ certV06 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV06, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_07 : certV03 ≠ certV07 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV07, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_08 : certV03 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV03, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_09 : certV03 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_10 : certV03 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV03, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_11 : certV03 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_12 : certV03 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_13 : certV03 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_14 : certV03 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_15 : certV03 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_16 : certV03 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV03, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_17 : certV03 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_18 : certV03 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV03, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_19 : certV03 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_20 : certV03 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_21 : certV03 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_22 : certV03 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_23 : certV03 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_24 : certV03 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_25 : certV03 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV03, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_26 : certV03 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_27 : certV03 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV03, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_28 : certV03 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_29 : certV03 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_30 : certV03 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV03, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV03_ne_31 : certV03 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV03, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_05 : certV04 ≠ certV05 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV05, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_06 : certV04 ≠ certV06 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV04, certV06, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_07 : certV04 ≠ certV07 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV07, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_08 : certV04 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_09 : certV04 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV04, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_10 : certV04 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_11 : certV04 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV04, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_12 : certV04 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_13 : certV04 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV04, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_14 : certV04 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_15 : certV04 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV04, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_16 : certV04 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_17 : certV04 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV04, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_18 : certV04 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_19 : certV04 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV04, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_20 : certV04 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_21 : certV04 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV04, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_22 : certV04 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_23 : certV04 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV04, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_24 : certV04 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV04, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_25 : certV04 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_26 : certV04 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV04, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_27 : certV04 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_28 : certV04 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV04, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_29 : certV04 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_30 : certV04 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV04, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV04_ne_31 : certV04 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV04, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_06 : certV05 ≠ certV06 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV06, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_07 : certV05 ≠ certV07 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV05, certV07, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_08 : certV05 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV05, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_09 : certV05 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_10 : certV05 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV05, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_11 : certV05 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_12 : certV05 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV05, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_13 : certV05 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_14 : certV05 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV05, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_15 : certV05 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_16 : certV05 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV05, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_17 : certV05 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_18 : certV05 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV05, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_19 : certV05 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_20 : certV05 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV05, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_21 : certV05 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_22 : certV05 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV05, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_23 : certV05 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_24 : certV05 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_25 : certV05 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV05, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_26 : certV05 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_27 : certV05 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV05, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_28 : certV05 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_29 : certV05 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV05, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_30 : certV05 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV05, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV05_ne_31 : certV05 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV05, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_07 : certV06 ≠ certV07 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV07, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_08 : certV06 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_09 : certV06 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV06, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_10 : certV06 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_11 : certV06 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV06, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_12 : certV06 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_13 : certV06 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV06, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_14 : certV06 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_15 : certV06 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV06, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_16 : certV06 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_17 : certV06 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV06, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_18 : certV06 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_19 : certV06 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV06, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_20 : certV06 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_21 : certV06 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV06, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_22 : certV06 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_23 : certV06 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV06, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_24 : certV06 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV06, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_25 : certV06 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_26 : certV06 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV06, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_27 : certV06 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_28 : certV06 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV06, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_29 : certV06 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_30 : certV06 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV06, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV06_ne_31 : certV06 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV06, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_08 : certV07 ≠ certV08 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV07, certV08, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_09 : certV07 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_10 : certV07 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV07, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_11 : certV07 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_12 : certV07 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV07, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_13 : certV07 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_14 : certV07 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV07, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_15 : certV07 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_16 : certV07 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV07, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_17 : certV07 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_18 : certV07 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV07, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_19 : certV07 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_20 : certV07 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV07, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_21 : certV07 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_22 : certV07 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV07, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_23 : certV07 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_24 : certV07 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_25 : certV07 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV07, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_26 : certV07 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_27 : certV07 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV07, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_28 : certV07 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_29 : certV07 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV07, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_30 : certV07 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV07, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV07_ne_31 : certV07 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV07, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_09 : certV08 ≠ certV09 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV09, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_10 : certV08 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV08, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_11 : certV08 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_12 : certV08 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV08, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_13 : certV08 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_14 : certV08 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV08, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_15 : certV08 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_16 : certV08 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV08, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_17 : certV08 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_18 : certV08 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV08, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_19 : certV08 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_20 : certV08 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV08, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_21 : certV08 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_22 : certV08 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV08, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_23 : certV08 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_24 : certV08 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_25 : certV08 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV08, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_26 : certV08 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_27 : certV08 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV08, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_28 : certV08 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_29 : certV08 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV08, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_30 : certV08 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV08, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV08_ne_31 : certV08 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV08, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_10 : certV09 ≠ certV10 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV10, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_11 : certV09 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV09, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_12 : certV09 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_13 : certV09 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV09, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_14 : certV09 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_15 : certV09 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV09, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_16 : certV09 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_17 : certV09 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV09, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_18 : certV09 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_19 : certV09 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV09, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_20 : certV09 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_21 : certV09 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV09, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_22 : certV09 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_23 : certV09 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV09, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_24 : certV09 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV09, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_25 : certV09 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_26 : certV09 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV09, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_27 : certV09 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_28 : certV09 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV09, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_29 : certV09 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_30 : certV09 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV09, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV09_ne_31 : certV09 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV09, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_11 : certV10 ≠ certV11 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV11, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_12 : certV10 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV10, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_13 : certV10 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_14 : certV10 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV10, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_15 : certV10 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_16 : certV10 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV10, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_17 : certV10 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_18 : certV10 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV10, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_19 : certV10 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_20 : certV10 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV10, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_21 : certV10 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_22 : certV10 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV10, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_23 : certV10 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_24 : certV10 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_25 : certV10 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV10, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_26 : certV10 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_27 : certV10 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV10, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_28 : certV10 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_29 : certV10 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV10, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_30 : certV10 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV10, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV10_ne_31 : certV10 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV10, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_12 : certV11 ≠ certV12 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV12, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_13 : certV11 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV11, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_14 : certV11 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_15 : certV11 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV11, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_16 : certV11 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_17 : certV11 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV11, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_18 : certV11 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_19 : certV11 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV11, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_20 : certV11 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_21 : certV11 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV11, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_22 : certV11 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_23 : certV11 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV11, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_24 : certV11 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV11, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_25 : certV11 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_26 : certV11 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV11, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_27 : certV11 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_28 : certV11 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV11, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_29 : certV11 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_30 : certV11 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV11, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV11_ne_31 : certV11 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV11, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_13 : certV12 ≠ certV13 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV13, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_14 : certV12 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV12, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_15 : certV12 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_16 : certV12 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV12, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_17 : certV12 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_18 : certV12 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV12, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_19 : certV12 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_20 : certV12 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV12, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_21 : certV12 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_22 : certV12 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV12, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_23 : certV12 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_24 : certV12 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_25 : certV12 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV12, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_26 : certV12 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_27 : certV12 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV12, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_28 : certV12 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_29 : certV12 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV12, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_30 : certV12 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV12, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV12_ne_31 : certV12 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV12, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_14 : certV13 ≠ certV14 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV14, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_15 : certV13 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV13, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_16 : certV13 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_17 : certV13 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV13, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_18 : certV13 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_19 : certV13 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV13, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_20 : certV13 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_21 : certV13 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV13, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_22 : certV13 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_23 : certV13 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV13, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_24 : certV13 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV13, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_25 : certV13 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_26 : certV13 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV13, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_27 : certV13 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_28 : certV13 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV13, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_29 : certV13 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_30 : certV13 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV13, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV13_ne_31 : certV13 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV13, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_15 : certV14 ≠ certV15 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV15, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_16 : certV14 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV14, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_17 : certV14 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_18 : certV14 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV14, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_19 : certV14 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_20 : certV14 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV14, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_21 : certV14 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_22 : certV14 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV14, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_23 : certV14 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_24 : certV14 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_25 : certV14 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV14, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_26 : certV14 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_27 : certV14 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV14, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_28 : certV14 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_29 : certV14 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV14, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_30 : certV14 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV14, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV14_ne_31 : certV14 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV14, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_16 : certV15 ≠ certV16 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV16, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_17 : certV15 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV15, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_18 : certV15 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_19 : certV15 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV15, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_20 : certV15 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_21 : certV15 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV15, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_22 : certV15 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_23 : certV15 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV15, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_24 : certV15 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV15, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_25 : certV15 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_26 : certV15 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV15, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_27 : certV15 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_28 : certV15 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV15, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_29 : certV15 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_30 : certV15 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 2) h
  simp only [certV15, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV15_ne_31 : certV15 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV15, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_17 : certV16 ≠ certV17 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV17, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_18 : certV16 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV16, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_19 : certV16 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_20 : certV16 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV16, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_21 : certV16 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_22 : certV16 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV16, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_23 : certV16 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_24 : certV16 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_25 : certV16 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV16, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_26 : certV16 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_27 : certV16 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV16, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_28 : certV16 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_29 : certV16 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV16, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_30 : certV16 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV16, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV16_ne_31 : certV16 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV16, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_18 : certV17 ≠ certV18 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV18, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_19 : certV17 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV17, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_20 : certV17 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_21 : certV17 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV17, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_22 : certV17 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_23 : certV17 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV17, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_24 : certV17 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV17, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_25 : certV17 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_26 : certV17 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV17, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_27 : certV17 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_28 : certV17 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV17, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_29 : certV17 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_30 : certV17 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV17, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV17_ne_31 : certV17 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV17, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_19 : certV18 ≠ certV19 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV19, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_20 : certV18 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV18, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_21 : certV18 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_22 : certV18 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV18, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_23 : certV18 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_24 : certV18 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_25 : certV18 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV18, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_26 : certV18 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_27 : certV18 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV18, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_28 : certV18 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_29 : certV18 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV18, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_30 : certV18 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV18, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV18_ne_31 : certV18 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV18, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_20 : certV19 ≠ certV20 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV19, certV20, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_21 : certV19 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV19, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_22 : certV19 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV19, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_23 : certV19 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV19, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_24 : certV19 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV19, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_25 : certV19 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV19, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_26 : certV19 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV19, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_27 : certV19 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV19, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_28 : certV19 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV19, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_29 : certV19 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV19, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_30 : certV19 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV19, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV19_ne_31 : certV19 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV19, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_21 : certV20 ≠ certV21 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV20, certV21, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_22 : certV20 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV20, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_23 : certV20 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV20, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_24 : certV20 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV20, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_25 : certV20 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV20, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_26 : certV20 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV20, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_27 : certV20 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV20, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_28 : certV20 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV20, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_29 : certV20 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV20, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_30 : certV20 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV20, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV20_ne_31 : certV20 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV20, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_22 : certV21 ≠ certV22 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV21, certV22, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_23 : certV21 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV21, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_24 : certV21 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV21, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_25 : certV21 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV21, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_26 : certV21 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV21, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_27 : certV21 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV21, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_28 : certV21 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV21, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_29 : certV21 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV21, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_30 : certV21 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV21, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV21_ne_31 : certV21 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV21, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_23 : certV22 ≠ certV23 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV22, certV23, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_24 : certV22 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV22, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_25 : certV22 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV22, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_26 : certV22 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV22, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_27 : certV22 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV22, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_28 : certV22 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV22, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_29 : certV22 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV22, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_30 : certV22 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV22, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV22_ne_31 : certV22 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV22, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_24 : certV23 ≠ certV24 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV23, certV24, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_25 : certV23 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV23, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_26 : certV23 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV23, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_27 : certV23 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV23, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_28 : certV23 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV23, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_29 : certV23 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV23, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_30 : certV23 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 3) h
  simp only [certV23, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV23_ne_31 : certV23 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV23, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_25 : certV24 ≠ certV25 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV24, certV25, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_26 : certV24 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV24, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_27 : certV24 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV24, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_28 : certV24 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV24, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_29 : certV24 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV24, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_30 : certV24 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV24, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV24_ne_31 : certV24 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV24, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV25_ne_26 : certV25 ≠ certV26 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV25, certV26, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV25_ne_27 : certV25 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV25, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV25_ne_28 : certV25 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV25, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV25_ne_29 : certV25 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV25, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV25_ne_30 : certV25 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV25, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV25_ne_31 : certV25 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV25, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV26_ne_27 : certV26 ≠ certV27 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV26, certV27, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV26_ne_28 : certV26 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV26, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV26_ne_29 : certV26 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV26, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV26_ne_30 : certV26 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV26, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV26_ne_31 : certV26 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV26, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV27_ne_28 : certV27 ≠ certV28 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV27, certV28, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV27_ne_29 : certV27 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV27, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV27_ne_30 : certV27 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV27, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV27_ne_31 : certV27 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  simp only [certV27, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV28_ne_29 : certV28 ≠ certV29 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV28, certV29, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV28_ne_30 : certV28 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV28, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV28_ne_31 : certV28 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV28, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV29_ne_30 : certV29 ≠ certV30 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV29, certV30, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV29_ne_31 : certV29 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 4) h
  simp only [certV29, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
theorem certV30_ne_31 : certV30 ≠ certV31 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  simp only [certV30, certV31, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  norm_num at hc
#print axioms certV01_ne_02
#print axioms certV30_ne_31

theorem certMkV01_ne_02 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV02 := by
  intro h
  exact certV01_ne_02 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV02_degree_lt_all h)
theorem certMkV01_ne_03 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV03 := by
  intro h
  exact certV01_ne_03 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV03_degree_lt_all h)
theorem certMkV01_ne_04 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV04 := by
  intro h
  exact certV01_ne_04 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV04_degree_lt_all h)
theorem certMkV01_ne_05 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV05 := by
  intro h
  exact certV01_ne_05 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV05_degree_lt_all h)
theorem certMkV01_ne_06 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV06 := by
  intro h
  exact certV01_ne_06 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV06_degree_lt_all h)
theorem certMkV01_ne_07 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV07 := by
  intro h
  exact certV01_ne_07 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV07_degree_lt_all h)
theorem certMkV01_ne_08 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV01_ne_08 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV08_degree_lt_all h)
theorem certMkV01_ne_09 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV01_ne_09 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV09_degree_lt_all h)
theorem certMkV01_ne_10 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV01_ne_10 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV10_degree_lt_all h)
theorem certMkV01_ne_11 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV01_ne_11 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV11_degree_lt_all h)
theorem certMkV01_ne_12 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV01_ne_12 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV12_degree_lt_all h)
theorem certMkV01_ne_13 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV01_ne_13 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV13_degree_lt_all h)
theorem certMkV01_ne_14 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV01_ne_14 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV14_degree_lt_all h)
theorem certMkV01_ne_15 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV01_ne_15 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV15_degree_lt_all h)
theorem certMkV01_ne_16 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV01_ne_16 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV16_degree_lt_all h)
theorem certMkV01_ne_17 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV01_ne_17 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV17_degree_lt_all h)
theorem certMkV01_ne_18 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV01_ne_18 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV18_degree_lt_all h)
theorem certMkV01_ne_19 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV01_ne_19 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV19_degree_lt_all h)
theorem certMkV01_ne_20 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV01_ne_20 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV20_degree_lt_all h)
theorem certMkV01_ne_21 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV01_ne_21 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV21_degree_lt_all h)
theorem certMkV01_ne_22 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV01_ne_22 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV22_degree_lt_all h)
theorem certMkV01_ne_23 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV01_ne_23 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV23_degree_lt_all h)
theorem certMkV01_ne_24 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV01_ne_24 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV24_degree_lt_all h)
theorem certMkV01_ne_25 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV01_ne_25 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV25_degree_lt_all h)
theorem certMkV01_ne_26 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV01_ne_26 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV26_degree_lt_all h)
theorem certMkV01_ne_27 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV01_ne_27 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV27_degree_lt_all h)
theorem certMkV01_ne_28 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV01_ne_28 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV28_degree_lt_all h)
theorem certMkV01_ne_29 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV01_ne_29 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV29_degree_lt_all h)
theorem certMkV01_ne_30 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV01_ne_30 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV30_degree_lt_all h)
theorem certMkV01_ne_31 : AdjoinRoot.mk f certV01 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV01_ne_31 (adjoin_mk_injective_below_11 certV01_degree_lt_all certV31_degree_lt_all h)
theorem certMkV02_ne_03 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV03 := by
  intro h
  exact certV02_ne_03 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV03_degree_lt_all h)
theorem certMkV02_ne_04 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV04 := by
  intro h
  exact certV02_ne_04 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV04_degree_lt_all h)
theorem certMkV02_ne_05 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV05 := by
  intro h
  exact certV02_ne_05 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV05_degree_lt_all h)
theorem certMkV02_ne_06 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV06 := by
  intro h
  exact certV02_ne_06 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV06_degree_lt_all h)
theorem certMkV02_ne_07 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV07 := by
  intro h
  exact certV02_ne_07 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV07_degree_lt_all h)
theorem certMkV02_ne_08 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV02_ne_08 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV08_degree_lt_all h)
theorem certMkV02_ne_09 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV02_ne_09 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV09_degree_lt_all h)
theorem certMkV02_ne_10 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV02_ne_10 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV10_degree_lt_all h)
theorem certMkV02_ne_11 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV02_ne_11 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV11_degree_lt_all h)
theorem certMkV02_ne_12 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV02_ne_12 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV12_degree_lt_all h)
theorem certMkV02_ne_13 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV02_ne_13 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV13_degree_lt_all h)
theorem certMkV02_ne_14 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV02_ne_14 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV14_degree_lt_all h)
theorem certMkV02_ne_15 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV02_ne_15 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV15_degree_lt_all h)
theorem certMkV02_ne_16 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV02_ne_16 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV16_degree_lt_all h)
theorem certMkV02_ne_17 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV02_ne_17 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV17_degree_lt_all h)
theorem certMkV02_ne_18 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV02_ne_18 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV18_degree_lt_all h)
theorem certMkV02_ne_19 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV02_ne_19 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV19_degree_lt_all h)
theorem certMkV02_ne_20 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV02_ne_20 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV20_degree_lt_all h)
theorem certMkV02_ne_21 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV02_ne_21 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV21_degree_lt_all h)
theorem certMkV02_ne_22 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV02_ne_22 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV22_degree_lt_all h)
theorem certMkV02_ne_23 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV02_ne_23 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV23_degree_lt_all h)
theorem certMkV02_ne_24 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV02_ne_24 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV24_degree_lt_all h)
theorem certMkV02_ne_25 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV02_ne_25 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV25_degree_lt_all h)
theorem certMkV02_ne_26 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV02_ne_26 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV26_degree_lt_all h)
theorem certMkV02_ne_27 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV02_ne_27 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV27_degree_lt_all h)
theorem certMkV02_ne_28 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV02_ne_28 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV28_degree_lt_all h)
theorem certMkV02_ne_29 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV02_ne_29 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV29_degree_lt_all h)
theorem certMkV02_ne_30 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV02_ne_30 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV30_degree_lt_all h)
theorem certMkV02_ne_31 : AdjoinRoot.mk f certV02 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV02_ne_31 (adjoin_mk_injective_below_11 certV02_degree_lt_all certV31_degree_lt_all h)
theorem certMkV03_ne_04 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV04 := by
  intro h
  exact certV03_ne_04 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV04_degree_lt_all h)
theorem certMkV03_ne_05 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV05 := by
  intro h
  exact certV03_ne_05 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV05_degree_lt_all h)
theorem certMkV03_ne_06 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV06 := by
  intro h
  exact certV03_ne_06 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV06_degree_lt_all h)
theorem certMkV03_ne_07 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV07 := by
  intro h
  exact certV03_ne_07 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV07_degree_lt_all h)
theorem certMkV03_ne_08 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV03_ne_08 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV08_degree_lt_all h)
theorem certMkV03_ne_09 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV03_ne_09 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV09_degree_lt_all h)
theorem certMkV03_ne_10 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV03_ne_10 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV10_degree_lt_all h)
theorem certMkV03_ne_11 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV03_ne_11 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV11_degree_lt_all h)
theorem certMkV03_ne_12 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV03_ne_12 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV12_degree_lt_all h)
theorem certMkV03_ne_13 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV03_ne_13 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV13_degree_lt_all h)
theorem certMkV03_ne_14 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV03_ne_14 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV14_degree_lt_all h)
theorem certMkV03_ne_15 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV03_ne_15 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV15_degree_lt_all h)
theorem certMkV03_ne_16 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV03_ne_16 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV16_degree_lt_all h)
theorem certMkV03_ne_17 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV03_ne_17 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV17_degree_lt_all h)
theorem certMkV03_ne_18 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV03_ne_18 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV18_degree_lt_all h)
theorem certMkV03_ne_19 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV03_ne_19 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV19_degree_lt_all h)
theorem certMkV03_ne_20 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV03_ne_20 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV20_degree_lt_all h)
theorem certMkV03_ne_21 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV03_ne_21 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV21_degree_lt_all h)
theorem certMkV03_ne_22 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV03_ne_22 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV22_degree_lt_all h)
theorem certMkV03_ne_23 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV03_ne_23 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV23_degree_lt_all h)
theorem certMkV03_ne_24 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV03_ne_24 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV24_degree_lt_all h)
theorem certMkV03_ne_25 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV03_ne_25 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV25_degree_lt_all h)
theorem certMkV03_ne_26 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV03_ne_26 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV26_degree_lt_all h)
theorem certMkV03_ne_27 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV03_ne_27 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV27_degree_lt_all h)
theorem certMkV03_ne_28 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV03_ne_28 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV28_degree_lt_all h)
theorem certMkV03_ne_29 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV03_ne_29 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV29_degree_lt_all h)
theorem certMkV03_ne_30 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV03_ne_30 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV30_degree_lt_all h)
theorem certMkV03_ne_31 : AdjoinRoot.mk f certV03 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV03_ne_31 (adjoin_mk_injective_below_11 certV03_degree_lt_all certV31_degree_lt_all h)
theorem certMkV04_ne_05 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV05 := by
  intro h
  exact certV04_ne_05 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV05_degree_lt_all h)
theorem certMkV04_ne_06 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV06 := by
  intro h
  exact certV04_ne_06 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV06_degree_lt_all h)
theorem certMkV04_ne_07 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV07 := by
  intro h
  exact certV04_ne_07 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV07_degree_lt_all h)
theorem certMkV04_ne_08 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV04_ne_08 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV08_degree_lt_all h)
theorem certMkV04_ne_09 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV04_ne_09 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV09_degree_lt_all h)
theorem certMkV04_ne_10 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV04_ne_10 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV10_degree_lt_all h)
theorem certMkV04_ne_11 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV04_ne_11 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV11_degree_lt_all h)
theorem certMkV04_ne_12 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV04_ne_12 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV12_degree_lt_all h)
theorem certMkV04_ne_13 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV04_ne_13 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV13_degree_lt_all h)
theorem certMkV04_ne_14 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV04_ne_14 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV14_degree_lt_all h)
theorem certMkV04_ne_15 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV04_ne_15 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV15_degree_lt_all h)
theorem certMkV04_ne_16 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV04_ne_16 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV16_degree_lt_all h)
theorem certMkV04_ne_17 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV04_ne_17 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV17_degree_lt_all h)
theorem certMkV04_ne_18 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV04_ne_18 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV18_degree_lt_all h)
theorem certMkV04_ne_19 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV04_ne_19 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV19_degree_lt_all h)
theorem certMkV04_ne_20 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV04_ne_20 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV20_degree_lt_all h)
theorem certMkV04_ne_21 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV04_ne_21 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV21_degree_lt_all h)
theorem certMkV04_ne_22 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV04_ne_22 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV22_degree_lt_all h)
theorem certMkV04_ne_23 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV04_ne_23 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV23_degree_lt_all h)
theorem certMkV04_ne_24 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV04_ne_24 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV24_degree_lt_all h)
theorem certMkV04_ne_25 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV04_ne_25 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV25_degree_lt_all h)
theorem certMkV04_ne_26 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV04_ne_26 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV26_degree_lt_all h)
theorem certMkV04_ne_27 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV04_ne_27 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV27_degree_lt_all h)
theorem certMkV04_ne_28 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV04_ne_28 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV28_degree_lt_all h)
theorem certMkV04_ne_29 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV04_ne_29 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV29_degree_lt_all h)
theorem certMkV04_ne_30 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV04_ne_30 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV30_degree_lt_all h)
theorem certMkV04_ne_31 : AdjoinRoot.mk f certV04 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV04_ne_31 (adjoin_mk_injective_below_11 certV04_degree_lt_all certV31_degree_lt_all h)
theorem certMkV05_ne_06 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV06 := by
  intro h
  exact certV05_ne_06 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV06_degree_lt_all h)
theorem certMkV05_ne_07 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV07 := by
  intro h
  exact certV05_ne_07 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV07_degree_lt_all h)
theorem certMkV05_ne_08 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV05_ne_08 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV08_degree_lt_all h)
theorem certMkV05_ne_09 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV05_ne_09 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV09_degree_lt_all h)
theorem certMkV05_ne_10 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV05_ne_10 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV10_degree_lt_all h)
theorem certMkV05_ne_11 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV05_ne_11 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV11_degree_lt_all h)
theorem certMkV05_ne_12 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV05_ne_12 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV12_degree_lt_all h)
theorem certMkV05_ne_13 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV05_ne_13 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV13_degree_lt_all h)
theorem certMkV05_ne_14 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV05_ne_14 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV14_degree_lt_all h)
theorem certMkV05_ne_15 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV05_ne_15 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV15_degree_lt_all h)
theorem certMkV05_ne_16 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV05_ne_16 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV16_degree_lt_all h)
theorem certMkV05_ne_17 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV05_ne_17 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV17_degree_lt_all h)
theorem certMkV05_ne_18 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV05_ne_18 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV18_degree_lt_all h)
theorem certMkV05_ne_19 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV05_ne_19 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV19_degree_lt_all h)
theorem certMkV05_ne_20 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV05_ne_20 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV20_degree_lt_all h)
theorem certMkV05_ne_21 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV05_ne_21 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV21_degree_lt_all h)
theorem certMkV05_ne_22 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV05_ne_22 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV22_degree_lt_all h)
theorem certMkV05_ne_23 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV05_ne_23 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV23_degree_lt_all h)
theorem certMkV05_ne_24 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV05_ne_24 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV24_degree_lt_all h)
theorem certMkV05_ne_25 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV05_ne_25 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV25_degree_lt_all h)
theorem certMkV05_ne_26 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV05_ne_26 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV26_degree_lt_all h)
theorem certMkV05_ne_27 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV05_ne_27 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV27_degree_lt_all h)
theorem certMkV05_ne_28 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV05_ne_28 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV28_degree_lt_all h)
theorem certMkV05_ne_29 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV05_ne_29 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV29_degree_lt_all h)
theorem certMkV05_ne_30 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV05_ne_30 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV30_degree_lt_all h)
theorem certMkV05_ne_31 : AdjoinRoot.mk f certV05 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV05_ne_31 (adjoin_mk_injective_below_11 certV05_degree_lt_all certV31_degree_lt_all h)
theorem certMkV06_ne_07 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV07 := by
  intro h
  exact certV06_ne_07 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV07_degree_lt_all h)
theorem certMkV06_ne_08 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV06_ne_08 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV08_degree_lt_all h)
theorem certMkV06_ne_09 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV06_ne_09 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV09_degree_lt_all h)
theorem certMkV06_ne_10 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV06_ne_10 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV10_degree_lt_all h)
theorem certMkV06_ne_11 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV06_ne_11 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV11_degree_lt_all h)
theorem certMkV06_ne_12 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV06_ne_12 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV12_degree_lt_all h)
theorem certMkV06_ne_13 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV06_ne_13 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV13_degree_lt_all h)
theorem certMkV06_ne_14 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV06_ne_14 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV14_degree_lt_all h)
theorem certMkV06_ne_15 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV06_ne_15 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV15_degree_lt_all h)
theorem certMkV06_ne_16 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV06_ne_16 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV16_degree_lt_all h)
theorem certMkV06_ne_17 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV06_ne_17 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV17_degree_lt_all h)
theorem certMkV06_ne_18 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV06_ne_18 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV18_degree_lt_all h)
theorem certMkV06_ne_19 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV06_ne_19 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV19_degree_lt_all h)
theorem certMkV06_ne_20 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV06_ne_20 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV20_degree_lt_all h)
theorem certMkV06_ne_21 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV06_ne_21 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV21_degree_lt_all h)
theorem certMkV06_ne_22 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV06_ne_22 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV22_degree_lt_all h)
theorem certMkV06_ne_23 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV06_ne_23 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV23_degree_lt_all h)
theorem certMkV06_ne_24 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV06_ne_24 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV24_degree_lt_all h)
theorem certMkV06_ne_25 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV06_ne_25 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV25_degree_lt_all h)
theorem certMkV06_ne_26 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV06_ne_26 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV26_degree_lt_all h)
theorem certMkV06_ne_27 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV06_ne_27 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV27_degree_lt_all h)
theorem certMkV06_ne_28 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV06_ne_28 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV28_degree_lt_all h)
theorem certMkV06_ne_29 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV06_ne_29 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV29_degree_lt_all h)
theorem certMkV06_ne_30 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV06_ne_30 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV30_degree_lt_all h)
theorem certMkV06_ne_31 : AdjoinRoot.mk f certV06 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV06_ne_31 (adjoin_mk_injective_below_11 certV06_degree_lt_all certV31_degree_lt_all h)
theorem certMkV07_ne_08 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV08 := by
  intro h
  exact certV07_ne_08 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV08_degree_lt_all h)
theorem certMkV07_ne_09 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV07_ne_09 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV09_degree_lt_all h)
theorem certMkV07_ne_10 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV07_ne_10 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV10_degree_lt_all h)
theorem certMkV07_ne_11 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV07_ne_11 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV11_degree_lt_all h)
theorem certMkV07_ne_12 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV07_ne_12 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV12_degree_lt_all h)
theorem certMkV07_ne_13 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV07_ne_13 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV13_degree_lt_all h)
theorem certMkV07_ne_14 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV07_ne_14 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV14_degree_lt_all h)
theorem certMkV07_ne_15 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV07_ne_15 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV15_degree_lt_all h)
theorem certMkV07_ne_16 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV07_ne_16 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV16_degree_lt_all h)
theorem certMkV07_ne_17 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV07_ne_17 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV17_degree_lt_all h)
theorem certMkV07_ne_18 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV07_ne_18 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV18_degree_lt_all h)
theorem certMkV07_ne_19 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV07_ne_19 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV19_degree_lt_all h)
theorem certMkV07_ne_20 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV07_ne_20 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV20_degree_lt_all h)
theorem certMkV07_ne_21 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV07_ne_21 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV21_degree_lt_all h)
theorem certMkV07_ne_22 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV07_ne_22 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV22_degree_lt_all h)
theorem certMkV07_ne_23 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV07_ne_23 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV23_degree_lt_all h)
theorem certMkV07_ne_24 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV07_ne_24 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV24_degree_lt_all h)
theorem certMkV07_ne_25 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV07_ne_25 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV25_degree_lt_all h)
theorem certMkV07_ne_26 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV07_ne_26 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV26_degree_lt_all h)
theorem certMkV07_ne_27 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV07_ne_27 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV27_degree_lt_all h)
theorem certMkV07_ne_28 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV07_ne_28 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV28_degree_lt_all h)
theorem certMkV07_ne_29 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV07_ne_29 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV29_degree_lt_all h)
theorem certMkV07_ne_30 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV07_ne_30 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV30_degree_lt_all h)
theorem certMkV07_ne_31 : AdjoinRoot.mk f certV07 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV07_ne_31 (adjoin_mk_injective_below_11 certV07_degree_lt_all certV31_degree_lt_all h)
theorem certMkV08_ne_09 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV09 := by
  intro h
  exact certV08_ne_09 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV09_degree_lt_all h)
theorem certMkV08_ne_10 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV08_ne_10 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV10_degree_lt_all h)
theorem certMkV08_ne_11 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV08_ne_11 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV11_degree_lt_all h)
theorem certMkV08_ne_12 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV08_ne_12 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV12_degree_lt_all h)
theorem certMkV08_ne_13 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV08_ne_13 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV13_degree_lt_all h)
theorem certMkV08_ne_14 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV08_ne_14 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV14_degree_lt_all h)
theorem certMkV08_ne_15 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV08_ne_15 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV15_degree_lt_all h)
theorem certMkV08_ne_16 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV08_ne_16 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV16_degree_lt_all h)
theorem certMkV08_ne_17 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV08_ne_17 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV17_degree_lt_all h)
theorem certMkV08_ne_18 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV08_ne_18 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV18_degree_lt_all h)
theorem certMkV08_ne_19 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV08_ne_19 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV19_degree_lt_all h)
theorem certMkV08_ne_20 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV08_ne_20 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV20_degree_lt_all h)
theorem certMkV08_ne_21 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV08_ne_21 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV21_degree_lt_all h)
theorem certMkV08_ne_22 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV08_ne_22 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV22_degree_lt_all h)
theorem certMkV08_ne_23 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV08_ne_23 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV23_degree_lt_all h)
theorem certMkV08_ne_24 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV08_ne_24 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV24_degree_lt_all h)
theorem certMkV08_ne_25 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV08_ne_25 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV25_degree_lt_all h)
theorem certMkV08_ne_26 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV08_ne_26 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV26_degree_lt_all h)
theorem certMkV08_ne_27 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV08_ne_27 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV27_degree_lt_all h)
theorem certMkV08_ne_28 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV08_ne_28 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV28_degree_lt_all h)
theorem certMkV08_ne_29 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV08_ne_29 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV29_degree_lt_all h)
theorem certMkV08_ne_30 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV08_ne_30 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV30_degree_lt_all h)
theorem certMkV08_ne_31 : AdjoinRoot.mk f certV08 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV08_ne_31 (adjoin_mk_injective_below_11 certV08_degree_lt_all certV31_degree_lt_all h)
theorem certMkV09_ne_10 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV10 := by
  intro h
  exact certV09_ne_10 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV10_degree_lt_all h)
theorem certMkV09_ne_11 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV09_ne_11 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV11_degree_lt_all h)
theorem certMkV09_ne_12 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV09_ne_12 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV12_degree_lt_all h)
theorem certMkV09_ne_13 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV09_ne_13 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV13_degree_lt_all h)
theorem certMkV09_ne_14 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV09_ne_14 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV14_degree_lt_all h)
theorem certMkV09_ne_15 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV09_ne_15 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV15_degree_lt_all h)
theorem certMkV09_ne_16 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV09_ne_16 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV16_degree_lt_all h)
theorem certMkV09_ne_17 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV09_ne_17 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV17_degree_lt_all h)
theorem certMkV09_ne_18 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV09_ne_18 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV18_degree_lt_all h)
theorem certMkV09_ne_19 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV09_ne_19 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV19_degree_lt_all h)
theorem certMkV09_ne_20 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV09_ne_20 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV20_degree_lt_all h)
theorem certMkV09_ne_21 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV09_ne_21 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV21_degree_lt_all h)
theorem certMkV09_ne_22 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV09_ne_22 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV22_degree_lt_all h)
theorem certMkV09_ne_23 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV09_ne_23 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV23_degree_lt_all h)
theorem certMkV09_ne_24 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV09_ne_24 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV24_degree_lt_all h)
theorem certMkV09_ne_25 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV09_ne_25 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV25_degree_lt_all h)
theorem certMkV09_ne_26 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV09_ne_26 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV26_degree_lt_all h)
theorem certMkV09_ne_27 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV09_ne_27 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV27_degree_lt_all h)
theorem certMkV09_ne_28 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV09_ne_28 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV28_degree_lt_all h)
theorem certMkV09_ne_29 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV09_ne_29 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV29_degree_lt_all h)
theorem certMkV09_ne_30 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV09_ne_30 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV30_degree_lt_all h)
theorem certMkV09_ne_31 : AdjoinRoot.mk f certV09 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV09_ne_31 (adjoin_mk_injective_below_11 certV09_degree_lt_all certV31_degree_lt_all h)
theorem certMkV10_ne_11 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV11 := by
  intro h
  exact certV10_ne_11 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV11_degree_lt_all h)
theorem certMkV10_ne_12 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV10_ne_12 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV12_degree_lt_all h)
theorem certMkV10_ne_13 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV10_ne_13 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV13_degree_lt_all h)
theorem certMkV10_ne_14 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV10_ne_14 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV14_degree_lt_all h)
theorem certMkV10_ne_15 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV10_ne_15 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV15_degree_lt_all h)
theorem certMkV10_ne_16 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV10_ne_16 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV16_degree_lt_all h)
theorem certMkV10_ne_17 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV10_ne_17 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV17_degree_lt_all h)
theorem certMkV10_ne_18 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV10_ne_18 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV18_degree_lt_all h)
theorem certMkV10_ne_19 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV10_ne_19 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV19_degree_lt_all h)
theorem certMkV10_ne_20 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV10_ne_20 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV20_degree_lt_all h)
theorem certMkV10_ne_21 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV10_ne_21 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV21_degree_lt_all h)
theorem certMkV10_ne_22 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV10_ne_22 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV22_degree_lt_all h)
theorem certMkV10_ne_23 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV10_ne_23 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV23_degree_lt_all h)
theorem certMkV10_ne_24 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV10_ne_24 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV24_degree_lt_all h)
theorem certMkV10_ne_25 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV10_ne_25 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV25_degree_lt_all h)
theorem certMkV10_ne_26 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV10_ne_26 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV26_degree_lt_all h)
theorem certMkV10_ne_27 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV10_ne_27 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV27_degree_lt_all h)
theorem certMkV10_ne_28 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV10_ne_28 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV28_degree_lt_all h)
theorem certMkV10_ne_29 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV10_ne_29 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV29_degree_lt_all h)
theorem certMkV10_ne_30 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV10_ne_30 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV30_degree_lt_all h)
theorem certMkV10_ne_31 : AdjoinRoot.mk f certV10 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV10_ne_31 (adjoin_mk_injective_below_11 certV10_degree_lt_all certV31_degree_lt_all h)
theorem certMkV11_ne_12 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV12 := by
  intro h
  exact certV11_ne_12 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV12_degree_lt_all h)
theorem certMkV11_ne_13 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV11_ne_13 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV13_degree_lt_all h)
theorem certMkV11_ne_14 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV11_ne_14 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV14_degree_lt_all h)
theorem certMkV11_ne_15 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV11_ne_15 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV15_degree_lt_all h)
theorem certMkV11_ne_16 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV11_ne_16 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV16_degree_lt_all h)
theorem certMkV11_ne_17 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV11_ne_17 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV17_degree_lt_all h)
theorem certMkV11_ne_18 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV11_ne_18 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV18_degree_lt_all h)
theorem certMkV11_ne_19 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV11_ne_19 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV19_degree_lt_all h)
theorem certMkV11_ne_20 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV11_ne_20 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV20_degree_lt_all h)
theorem certMkV11_ne_21 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV11_ne_21 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV21_degree_lt_all h)
theorem certMkV11_ne_22 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV11_ne_22 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV22_degree_lt_all h)
theorem certMkV11_ne_23 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV11_ne_23 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV23_degree_lt_all h)
theorem certMkV11_ne_24 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV11_ne_24 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV24_degree_lt_all h)
theorem certMkV11_ne_25 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV11_ne_25 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV25_degree_lt_all h)
theorem certMkV11_ne_26 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV11_ne_26 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV26_degree_lt_all h)
theorem certMkV11_ne_27 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV11_ne_27 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV27_degree_lt_all h)
theorem certMkV11_ne_28 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV11_ne_28 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV28_degree_lt_all h)
theorem certMkV11_ne_29 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV11_ne_29 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV29_degree_lt_all h)
theorem certMkV11_ne_30 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV11_ne_30 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV30_degree_lt_all h)
theorem certMkV11_ne_31 : AdjoinRoot.mk f certV11 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV11_ne_31 (adjoin_mk_injective_below_11 certV11_degree_lt_all certV31_degree_lt_all h)
theorem certMkV12_ne_13 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV13 := by
  intro h
  exact certV12_ne_13 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV13_degree_lt_all h)
theorem certMkV12_ne_14 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV12_ne_14 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV14_degree_lt_all h)
theorem certMkV12_ne_15 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV12_ne_15 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV15_degree_lt_all h)
theorem certMkV12_ne_16 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV12_ne_16 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV16_degree_lt_all h)
theorem certMkV12_ne_17 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV12_ne_17 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV17_degree_lt_all h)
theorem certMkV12_ne_18 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV12_ne_18 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV18_degree_lt_all h)
theorem certMkV12_ne_19 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV12_ne_19 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV19_degree_lt_all h)
theorem certMkV12_ne_20 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV12_ne_20 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV20_degree_lt_all h)
theorem certMkV12_ne_21 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV12_ne_21 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV21_degree_lt_all h)
theorem certMkV12_ne_22 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV12_ne_22 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV22_degree_lt_all h)
theorem certMkV12_ne_23 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV12_ne_23 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV23_degree_lt_all h)
theorem certMkV12_ne_24 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV12_ne_24 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV24_degree_lt_all h)
theorem certMkV12_ne_25 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV12_ne_25 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV25_degree_lt_all h)
theorem certMkV12_ne_26 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV12_ne_26 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV26_degree_lt_all h)
theorem certMkV12_ne_27 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV12_ne_27 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV27_degree_lt_all h)
theorem certMkV12_ne_28 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV12_ne_28 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV28_degree_lt_all h)
theorem certMkV12_ne_29 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV12_ne_29 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV29_degree_lt_all h)
theorem certMkV12_ne_30 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV12_ne_30 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV30_degree_lt_all h)
theorem certMkV12_ne_31 : AdjoinRoot.mk f certV12 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV12_ne_31 (adjoin_mk_injective_below_11 certV12_degree_lt_all certV31_degree_lt_all h)
theorem certMkV13_ne_14 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV14 := by
  intro h
  exact certV13_ne_14 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV14_degree_lt_all h)
theorem certMkV13_ne_15 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV13_ne_15 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV15_degree_lt_all h)
theorem certMkV13_ne_16 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV13_ne_16 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV16_degree_lt_all h)
theorem certMkV13_ne_17 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV13_ne_17 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV17_degree_lt_all h)
theorem certMkV13_ne_18 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV13_ne_18 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV18_degree_lt_all h)
theorem certMkV13_ne_19 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV13_ne_19 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV19_degree_lt_all h)
theorem certMkV13_ne_20 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV13_ne_20 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV20_degree_lt_all h)
theorem certMkV13_ne_21 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV13_ne_21 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV21_degree_lt_all h)
theorem certMkV13_ne_22 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV13_ne_22 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV22_degree_lt_all h)
theorem certMkV13_ne_23 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV13_ne_23 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV23_degree_lt_all h)
theorem certMkV13_ne_24 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV13_ne_24 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV24_degree_lt_all h)
theorem certMkV13_ne_25 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV13_ne_25 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV25_degree_lt_all h)
theorem certMkV13_ne_26 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV13_ne_26 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV26_degree_lt_all h)
theorem certMkV13_ne_27 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV13_ne_27 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV27_degree_lt_all h)
theorem certMkV13_ne_28 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV13_ne_28 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV28_degree_lt_all h)
theorem certMkV13_ne_29 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV13_ne_29 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV29_degree_lt_all h)
theorem certMkV13_ne_30 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV13_ne_30 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV30_degree_lt_all h)
theorem certMkV13_ne_31 : AdjoinRoot.mk f certV13 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV13_ne_31 (adjoin_mk_injective_below_11 certV13_degree_lt_all certV31_degree_lt_all h)
theorem certMkV14_ne_15 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV15 := by
  intro h
  exact certV14_ne_15 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV15_degree_lt_all h)
theorem certMkV14_ne_16 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV14_ne_16 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV16_degree_lt_all h)
theorem certMkV14_ne_17 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV14_ne_17 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV17_degree_lt_all h)
theorem certMkV14_ne_18 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV14_ne_18 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV18_degree_lt_all h)
theorem certMkV14_ne_19 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV14_ne_19 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV19_degree_lt_all h)
theorem certMkV14_ne_20 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV14_ne_20 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV20_degree_lt_all h)
theorem certMkV14_ne_21 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV14_ne_21 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV21_degree_lt_all h)
theorem certMkV14_ne_22 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV14_ne_22 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV22_degree_lt_all h)
theorem certMkV14_ne_23 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV14_ne_23 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV23_degree_lt_all h)
theorem certMkV14_ne_24 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV14_ne_24 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV24_degree_lt_all h)
theorem certMkV14_ne_25 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV14_ne_25 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV25_degree_lt_all h)
theorem certMkV14_ne_26 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV14_ne_26 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV26_degree_lt_all h)
theorem certMkV14_ne_27 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV14_ne_27 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV27_degree_lt_all h)
theorem certMkV14_ne_28 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV14_ne_28 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV28_degree_lt_all h)
theorem certMkV14_ne_29 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV14_ne_29 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV29_degree_lt_all h)
theorem certMkV14_ne_30 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV14_ne_30 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV30_degree_lt_all h)
theorem certMkV14_ne_31 : AdjoinRoot.mk f certV14 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV14_ne_31 (adjoin_mk_injective_below_11 certV14_degree_lt_all certV31_degree_lt_all h)
theorem certMkV15_ne_16 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV16 := by
  intro h
  exact certV15_ne_16 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV16_degree_lt_all h)
theorem certMkV15_ne_17 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV15_ne_17 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV17_degree_lt_all h)
theorem certMkV15_ne_18 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV15_ne_18 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV18_degree_lt_all h)
theorem certMkV15_ne_19 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV15_ne_19 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV19_degree_lt_all h)
theorem certMkV15_ne_20 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV15_ne_20 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV20_degree_lt_all h)
theorem certMkV15_ne_21 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV15_ne_21 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV21_degree_lt_all h)
theorem certMkV15_ne_22 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV15_ne_22 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV22_degree_lt_all h)
theorem certMkV15_ne_23 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV15_ne_23 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV23_degree_lt_all h)
theorem certMkV15_ne_24 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV15_ne_24 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV24_degree_lt_all h)
theorem certMkV15_ne_25 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV15_ne_25 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV25_degree_lt_all h)
theorem certMkV15_ne_26 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV15_ne_26 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV26_degree_lt_all h)
theorem certMkV15_ne_27 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV15_ne_27 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV27_degree_lt_all h)
theorem certMkV15_ne_28 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV15_ne_28 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV28_degree_lt_all h)
theorem certMkV15_ne_29 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV15_ne_29 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV29_degree_lt_all h)
theorem certMkV15_ne_30 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV15_ne_30 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV30_degree_lt_all h)
theorem certMkV15_ne_31 : AdjoinRoot.mk f certV15 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV15_ne_31 (adjoin_mk_injective_below_11 certV15_degree_lt_all certV31_degree_lt_all h)
theorem certMkV16_ne_17 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV17 := by
  intro h
  exact certV16_ne_17 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV17_degree_lt_all h)
theorem certMkV16_ne_18 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV16_ne_18 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV18_degree_lt_all h)
theorem certMkV16_ne_19 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV16_ne_19 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV19_degree_lt_all h)
theorem certMkV16_ne_20 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV16_ne_20 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV20_degree_lt_all h)
theorem certMkV16_ne_21 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV16_ne_21 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV21_degree_lt_all h)
theorem certMkV16_ne_22 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV16_ne_22 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV22_degree_lt_all h)
theorem certMkV16_ne_23 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV16_ne_23 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV23_degree_lt_all h)
theorem certMkV16_ne_24 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV16_ne_24 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV24_degree_lt_all h)
theorem certMkV16_ne_25 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV16_ne_25 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV25_degree_lt_all h)
theorem certMkV16_ne_26 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV16_ne_26 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV26_degree_lt_all h)
theorem certMkV16_ne_27 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV16_ne_27 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV27_degree_lt_all h)
theorem certMkV16_ne_28 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV16_ne_28 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV28_degree_lt_all h)
theorem certMkV16_ne_29 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV16_ne_29 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV29_degree_lt_all h)
theorem certMkV16_ne_30 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV16_ne_30 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV30_degree_lt_all h)
theorem certMkV16_ne_31 : AdjoinRoot.mk f certV16 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV16_ne_31 (adjoin_mk_injective_below_11 certV16_degree_lt_all certV31_degree_lt_all h)
theorem certMkV17_ne_18 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV18 := by
  intro h
  exact certV17_ne_18 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV18_degree_lt_all h)
theorem certMkV17_ne_19 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV17_ne_19 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV19_degree_lt_all h)
theorem certMkV17_ne_20 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV17_ne_20 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV20_degree_lt_all h)
theorem certMkV17_ne_21 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV17_ne_21 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV21_degree_lt_all h)
theorem certMkV17_ne_22 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV17_ne_22 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV22_degree_lt_all h)
theorem certMkV17_ne_23 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV17_ne_23 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV23_degree_lt_all h)
theorem certMkV17_ne_24 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV17_ne_24 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV24_degree_lt_all h)
theorem certMkV17_ne_25 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV17_ne_25 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV25_degree_lt_all h)
theorem certMkV17_ne_26 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV17_ne_26 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV26_degree_lt_all h)
theorem certMkV17_ne_27 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV17_ne_27 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV27_degree_lt_all h)
theorem certMkV17_ne_28 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV17_ne_28 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV28_degree_lt_all h)
theorem certMkV17_ne_29 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV17_ne_29 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV29_degree_lt_all h)
theorem certMkV17_ne_30 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV17_ne_30 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV30_degree_lt_all h)
theorem certMkV17_ne_31 : AdjoinRoot.mk f certV17 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV17_ne_31 (adjoin_mk_injective_below_11 certV17_degree_lt_all certV31_degree_lt_all h)
theorem certMkV18_ne_19 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV19 := by
  intro h
  exact certV18_ne_19 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV19_degree_lt_all h)
theorem certMkV18_ne_20 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV18_ne_20 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV20_degree_lt_all h)
theorem certMkV18_ne_21 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV18_ne_21 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV21_degree_lt_all h)
theorem certMkV18_ne_22 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV18_ne_22 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV22_degree_lt_all h)
theorem certMkV18_ne_23 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV18_ne_23 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV23_degree_lt_all h)
theorem certMkV18_ne_24 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV18_ne_24 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV24_degree_lt_all h)
theorem certMkV18_ne_25 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV18_ne_25 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV25_degree_lt_all h)
theorem certMkV18_ne_26 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV18_ne_26 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV26_degree_lt_all h)
theorem certMkV18_ne_27 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV18_ne_27 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV27_degree_lt_all h)
theorem certMkV18_ne_28 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV18_ne_28 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV28_degree_lt_all h)
theorem certMkV18_ne_29 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV18_ne_29 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV29_degree_lt_all h)
theorem certMkV18_ne_30 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV18_ne_30 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV30_degree_lt_all h)
theorem certMkV18_ne_31 : AdjoinRoot.mk f certV18 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV18_ne_31 (adjoin_mk_injective_below_11 certV18_degree_lt_all certV31_degree_lt_all h)
theorem certMkV19_ne_20 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV20 := by
  intro h
  exact certV19_ne_20 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV20_degree_lt_all h)
theorem certMkV19_ne_21 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV19_ne_21 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV21_degree_lt_all h)
theorem certMkV19_ne_22 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV19_ne_22 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV22_degree_lt_all h)
theorem certMkV19_ne_23 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV19_ne_23 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV23_degree_lt_all h)
theorem certMkV19_ne_24 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV19_ne_24 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV24_degree_lt_all h)
theorem certMkV19_ne_25 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV19_ne_25 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV25_degree_lt_all h)
theorem certMkV19_ne_26 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV19_ne_26 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV26_degree_lt_all h)
theorem certMkV19_ne_27 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV19_ne_27 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV27_degree_lt_all h)
theorem certMkV19_ne_28 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV19_ne_28 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV28_degree_lt_all h)
theorem certMkV19_ne_29 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV19_ne_29 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV29_degree_lt_all h)
theorem certMkV19_ne_30 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV19_ne_30 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV30_degree_lt_all h)
theorem certMkV19_ne_31 : AdjoinRoot.mk f certV19 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV19_ne_31 (adjoin_mk_injective_below_11 certV19_degree_lt_all certV31_degree_lt_all h)
theorem certMkV20_ne_21 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV21 := by
  intro h
  exact certV20_ne_21 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV21_degree_lt_all h)
theorem certMkV20_ne_22 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV20_ne_22 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV22_degree_lt_all h)
theorem certMkV20_ne_23 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV20_ne_23 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV23_degree_lt_all h)
theorem certMkV20_ne_24 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV20_ne_24 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV24_degree_lt_all h)
theorem certMkV20_ne_25 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV20_ne_25 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV25_degree_lt_all h)
theorem certMkV20_ne_26 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV20_ne_26 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV26_degree_lt_all h)
theorem certMkV20_ne_27 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV20_ne_27 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV27_degree_lt_all h)
theorem certMkV20_ne_28 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV20_ne_28 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV28_degree_lt_all h)
theorem certMkV20_ne_29 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV20_ne_29 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV29_degree_lt_all h)
theorem certMkV20_ne_30 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV20_ne_30 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV30_degree_lt_all h)
theorem certMkV20_ne_31 : AdjoinRoot.mk f certV20 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV20_ne_31 (adjoin_mk_injective_below_11 certV20_degree_lt_all certV31_degree_lt_all h)
theorem certMkV21_ne_22 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV22 := by
  intro h
  exact certV21_ne_22 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV22_degree_lt_all h)
theorem certMkV21_ne_23 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV21_ne_23 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV23_degree_lt_all h)
theorem certMkV21_ne_24 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV21_ne_24 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV24_degree_lt_all h)
theorem certMkV21_ne_25 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV21_ne_25 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV25_degree_lt_all h)
theorem certMkV21_ne_26 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV21_ne_26 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV26_degree_lt_all h)
theorem certMkV21_ne_27 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV21_ne_27 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV27_degree_lt_all h)
theorem certMkV21_ne_28 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV21_ne_28 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV28_degree_lt_all h)
theorem certMkV21_ne_29 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV21_ne_29 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV29_degree_lt_all h)
theorem certMkV21_ne_30 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV21_ne_30 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV30_degree_lt_all h)
theorem certMkV21_ne_31 : AdjoinRoot.mk f certV21 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV21_ne_31 (adjoin_mk_injective_below_11 certV21_degree_lt_all certV31_degree_lt_all h)
theorem certMkV22_ne_23 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV23 := by
  intro h
  exact certV22_ne_23 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV23_degree_lt_all h)
theorem certMkV22_ne_24 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV22_ne_24 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV24_degree_lt_all h)
theorem certMkV22_ne_25 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV22_ne_25 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV25_degree_lt_all h)
theorem certMkV22_ne_26 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV22_ne_26 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV26_degree_lt_all h)
theorem certMkV22_ne_27 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV22_ne_27 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV27_degree_lt_all h)
theorem certMkV22_ne_28 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV22_ne_28 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV28_degree_lt_all h)
theorem certMkV22_ne_29 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV22_ne_29 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV29_degree_lt_all h)
theorem certMkV22_ne_30 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV22_ne_30 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV30_degree_lt_all h)
theorem certMkV22_ne_31 : AdjoinRoot.mk f certV22 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV22_ne_31 (adjoin_mk_injective_below_11 certV22_degree_lt_all certV31_degree_lt_all h)
theorem certMkV23_ne_24 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV24 := by
  intro h
  exact certV23_ne_24 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV24_degree_lt_all h)
theorem certMkV23_ne_25 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV23_ne_25 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV25_degree_lt_all h)
theorem certMkV23_ne_26 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV23_ne_26 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV26_degree_lt_all h)
theorem certMkV23_ne_27 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV23_ne_27 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV27_degree_lt_all h)
theorem certMkV23_ne_28 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV23_ne_28 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV28_degree_lt_all h)
theorem certMkV23_ne_29 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV23_ne_29 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV29_degree_lt_all h)
theorem certMkV23_ne_30 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV23_ne_30 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV30_degree_lt_all h)
theorem certMkV23_ne_31 : AdjoinRoot.mk f certV23 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV23_ne_31 (adjoin_mk_injective_below_11 certV23_degree_lt_all certV31_degree_lt_all h)
theorem certMkV24_ne_25 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV25 := by
  intro h
  exact certV24_ne_25 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV25_degree_lt_all h)
theorem certMkV24_ne_26 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV24_ne_26 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV26_degree_lt_all h)
theorem certMkV24_ne_27 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV24_ne_27 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV27_degree_lt_all h)
theorem certMkV24_ne_28 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV24_ne_28 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV28_degree_lt_all h)
theorem certMkV24_ne_29 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV24_ne_29 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV29_degree_lt_all h)
theorem certMkV24_ne_30 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV24_ne_30 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV30_degree_lt_all h)
theorem certMkV24_ne_31 : AdjoinRoot.mk f certV24 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV24_ne_31 (adjoin_mk_injective_below_11 certV24_degree_lt_all certV31_degree_lt_all h)
theorem certMkV25_ne_26 : AdjoinRoot.mk f certV25 ≠ AdjoinRoot.mk f certV26 := by
  intro h
  exact certV25_ne_26 (adjoin_mk_injective_below_11 certV25_degree_lt_all certV26_degree_lt_all h)
theorem certMkV25_ne_27 : AdjoinRoot.mk f certV25 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV25_ne_27 (adjoin_mk_injective_below_11 certV25_degree_lt_all certV27_degree_lt_all h)
theorem certMkV25_ne_28 : AdjoinRoot.mk f certV25 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV25_ne_28 (adjoin_mk_injective_below_11 certV25_degree_lt_all certV28_degree_lt_all h)
theorem certMkV25_ne_29 : AdjoinRoot.mk f certV25 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV25_ne_29 (adjoin_mk_injective_below_11 certV25_degree_lt_all certV29_degree_lt_all h)
theorem certMkV25_ne_30 : AdjoinRoot.mk f certV25 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV25_ne_30 (adjoin_mk_injective_below_11 certV25_degree_lt_all certV30_degree_lt_all h)
theorem certMkV25_ne_31 : AdjoinRoot.mk f certV25 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV25_ne_31 (adjoin_mk_injective_below_11 certV25_degree_lt_all certV31_degree_lt_all h)
theorem certMkV26_ne_27 : AdjoinRoot.mk f certV26 ≠ AdjoinRoot.mk f certV27 := by
  intro h
  exact certV26_ne_27 (adjoin_mk_injective_below_11 certV26_degree_lt_all certV27_degree_lt_all h)
theorem certMkV26_ne_28 : AdjoinRoot.mk f certV26 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV26_ne_28 (adjoin_mk_injective_below_11 certV26_degree_lt_all certV28_degree_lt_all h)
theorem certMkV26_ne_29 : AdjoinRoot.mk f certV26 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV26_ne_29 (adjoin_mk_injective_below_11 certV26_degree_lt_all certV29_degree_lt_all h)
theorem certMkV26_ne_30 : AdjoinRoot.mk f certV26 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV26_ne_30 (adjoin_mk_injective_below_11 certV26_degree_lt_all certV30_degree_lt_all h)
theorem certMkV26_ne_31 : AdjoinRoot.mk f certV26 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV26_ne_31 (adjoin_mk_injective_below_11 certV26_degree_lt_all certV31_degree_lt_all h)
theorem certMkV27_ne_28 : AdjoinRoot.mk f certV27 ≠ AdjoinRoot.mk f certV28 := by
  intro h
  exact certV27_ne_28 (adjoin_mk_injective_below_11 certV27_degree_lt_all certV28_degree_lt_all h)
theorem certMkV27_ne_29 : AdjoinRoot.mk f certV27 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV27_ne_29 (adjoin_mk_injective_below_11 certV27_degree_lt_all certV29_degree_lt_all h)
theorem certMkV27_ne_30 : AdjoinRoot.mk f certV27 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV27_ne_30 (adjoin_mk_injective_below_11 certV27_degree_lt_all certV30_degree_lt_all h)
theorem certMkV27_ne_31 : AdjoinRoot.mk f certV27 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV27_ne_31 (adjoin_mk_injective_below_11 certV27_degree_lt_all certV31_degree_lt_all h)
theorem certMkV28_ne_29 : AdjoinRoot.mk f certV28 ≠ AdjoinRoot.mk f certV29 := by
  intro h
  exact certV28_ne_29 (adjoin_mk_injective_below_11 certV28_degree_lt_all certV29_degree_lt_all h)
theorem certMkV28_ne_30 : AdjoinRoot.mk f certV28 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV28_ne_30 (adjoin_mk_injective_below_11 certV28_degree_lt_all certV30_degree_lt_all h)
theorem certMkV28_ne_31 : AdjoinRoot.mk f certV28 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV28_ne_31 (adjoin_mk_injective_below_11 certV28_degree_lt_all certV31_degree_lt_all h)
theorem certMkV29_ne_30 : AdjoinRoot.mk f certV29 ≠ AdjoinRoot.mk f certV30 := by
  intro h
  exact certV29_ne_30 (adjoin_mk_injective_below_11 certV29_degree_lt_all certV30_degree_lt_all h)
theorem certMkV29_ne_31 : AdjoinRoot.mk f certV29 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV29_ne_31 (adjoin_mk_injective_below_11 certV29_degree_lt_all certV31_degree_lt_all h)
theorem certMkV30_ne_31 : AdjoinRoot.mk f certV30 ≠ AdjoinRoot.mk f certV31 := by
  intro h
  exact certV30_ne_31 (adjoin_mk_injective_below_11 certV30_degree_lt_all certV31_degree_lt_all h)
#print axioms certMkV01_ne_02
#print axioms certMkV30_ne_31


