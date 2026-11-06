import Carlet.N11DistinctProbe
open Polynomial
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem certCombo01 : certV01 = certV01 := by
  rfl
theorem certCombo02 : certV02 = certV02 := by
  rfl
theorem certCombo03 : certV03 = certV01 + certV02 := by
  unfold certV03 certV01 certV02
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo04 : certV04 = certV04 := by
  rfl
theorem certCombo05 : certV05 = certV01 + certV04 := by
  unfold certV05 certV01 certV04
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo06 : certV06 = certV02 + certV04 := by
  unfold certV06 certV02 certV04
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo07 : certV07 = certV01 + certV02 + certV04 := by
  unfold certV07 certV01 certV02 certV04
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo08 : certV08 = certV08 := by
  rfl
theorem certCombo09 : certV09 = certV01 + certV08 := by
  unfold certV09 certV01 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo10 : certV10 = certV02 + certV08 := by
  unfold certV10 certV02 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo11 : certV11 = certV01 + certV02 + certV08 := by
  unfold certV11 certV01 certV02 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo12 : certV12 = certV04 + certV08 := by
  unfold certV12 certV04 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo13 : certV13 = certV01 + certV04 + certV08 := by
  unfold certV13 certV01 certV04 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo14 : certV14 = certV02 + certV04 + certV08 := by
  unfold certV14 certV02 certV04 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo15 : certV15 = certV01 + certV02 + certV04 + certV08 := by
  unfold certV15 certV01 certV02 certV04 certV08
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo16 : certV16 = certV16 := by
  rfl
theorem certCombo17 : certV17 = certV01 + certV16 := by
  unfold certV17 certV01 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo18 : certV18 = certV02 + certV16 := by
  unfold certV18 certV02 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo19 : certV19 = certV01 + certV02 + certV16 := by
  unfold certV19 certV01 certV02 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo20 : certV20 = certV04 + certV16 := by
  unfold certV20 certV04 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo21 : certV21 = certV01 + certV04 + certV16 := by
  unfold certV21 certV01 certV04 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo22 : certV22 = certV02 + certV04 + certV16 := by
  unfold certV22 certV02 certV04 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo23 : certV23 = certV01 + certV02 + certV04 + certV16 := by
  unfold certV23 certV01 certV02 certV04 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo24 : certV24 = certV08 + certV16 := by
  unfold certV24 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo25 : certV25 = certV01 + certV08 + certV16 := by
  unfold certV25 certV01 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo26 : certV26 = certV02 + certV08 + certV16 := by
  unfold certV26 certV02 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo27 : certV27 = certV01 + certV02 + certV08 + certV16 := by
  unfold certV27 certV01 certV02 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo28 : certV28 = certV04 + certV08 + certV16 := by
  unfold certV28 certV04 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo29 : certV29 = certV01 + certV04 + certV08 + certV16 := by
  unfold certV29 certV01 certV04 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo30 : certV30 = certV02 + certV04 + certV08 + certV16 := by
  unfold certV30 certV02 certV04 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
theorem certCombo31 : certV31 = certV01 + certV02 + certV04 + certV08 + certV16 := by
  unfold certV31 certV01 certV02 certV04 certV08 certV16
  ring_nf <;> simp [c2,c3,c4,c5,c6,c7,c8]
#print axioms certCombo01
#print axioms certCombo31



