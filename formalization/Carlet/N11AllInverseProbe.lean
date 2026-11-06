import Carlet.Frobenius11Scratch
import Mathlib.Tactic
import Mathlib.RingTheory.AdjoinRoot
open Polynomial
noncomputable section
set_option linter.unusedSimpArgs false
def certV01 : P := 1
def certI01 : P := 1
def certQ01 : P := 0
lemma certInvPoly01 : certV01 * certI01 + 1 = f * certQ01 := by
  unfold certV01 certI01 certQ01 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV02 : P := X^4 + X^5 + X^8 + X^9 + X^10
def certI02 : P := X^2 + X^3 + X^4 + X^6 + X^7 + X^9 + X^10
def certQ02 : P := 1 + X^2 + X^4 + X^9
lemma certInvPoly02 : certV02 * certI02 + 1 = f * certQ02 := by
  unfold certV02 certI02 certQ02 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV03 : P := 1 + X^4 + X^5 + X^8 + X^9 + X^10
def certI03 : P := 1 + X + X^3 + X^4 + X^6 + X^8 + X^9 + X^10
def certQ03 : P := X + X^7 + X^9
lemma certInvPoly03 : certV03 * certI03 + 1 = f * certQ03 := by
  unfold certV03 certI03 certQ03 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV04 : P := X + X^6 + X^7 + X^8 + X^10
def certI04 : P := X^2 + X^3 + X^6 + X^7 + X^8 + X^10
def certQ04 : P := 1 + X^2 + X^3 + X^5 + X^9
lemma certInvPoly04 : certV04 * certI04 + 1 = f * certQ04 := by
  unfold certV04 certI04 certQ04 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV05 : P := 1 + X + X^6 + X^7 + X^8 + X^10
def certI05 : P := X^2 + X^3 + X^6 + X^8
def certQ05 : P := 1 + X^4 + X^7
lemma certInvPoly05 : certV05 * certI05 + 1 = f * certQ05 := by
  unfold certV05 certI05 certQ05 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV06 : P := X + X^4 + X^5 + X^6 + X^7 + X^9
def certI06 : P := X + X^2 + X^7 + X^8 + X^10
def certQ06 : P := 1 + X^3 + X^8
lemma certInvPoly06 : certV06 * certI06 + 1 = f * certQ06 := by
  unfold certV06 certI06 certQ06 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV07 : P := 1 + X + X^4 + X^5 + X^6 + X^7 + X^9
def certI07 : P := X^3 + X^5 + X^6 + X^7 + X^9
def certQ07 : P := 1 + X^2 + X^3 + X^7
lemma certInvPoly07 : certV07 * certI07 + 1 = f * certQ07 := by
  unfold certV07 certI07 certQ07 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV08 : P := 1 + X^3 + X^5 + X^6 + X^8
def certI08 : P := X^7 + X^8 + X^9 + X^10
def certQ08 : P := 1 + X^2 + X^4 + X^6 + X^7
lemma certInvPoly08 : certV08 * certI08 + 1 = f * certQ08 := by
  unfold certV08 certI08 certQ08 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV09 : P := X^3 + X^5 + X^6 + X^8
def certI09 : P := X + X^2 + X^3 + X^4 + X^6 + X^8
def certQ09 : P := 1 + X^2 + X^5
lemma certInvPoly09 : certV09 * certI09 + 1 = f * certQ09 := by
  unfold certV09 certI09 certQ09 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV10 : P := 1 + X^3 + X^4 + X^6 + X^9 + X^10
def certI10 : P := X^3 + X^4 + X^6 + X^7 + X^8 + X^9 + X^10
def certQ10 : P := 1 + X^2 + X^3 + X^5 + X^9
lemma certInvPoly10 : certV10 * certI10 + 1 = f * certQ10 := by
  unfold certV10 certI10 certQ10 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV11 : P := X^3 + X^4 + X^6 + X^9 + X^10
def certI11 : P := X^2 + X^3 + X^8 + X^9 + X^10
def certQ11 : P := 1 + X^2 + X^4 + X^5 + X^6 + X^9
lemma certInvPoly11 : certV11 * certI11 + 1 = f * certQ11 := by
  unfold certV11 certI11 certQ11 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV12 : P := 1 + X + X^3 + X^5 + X^7 + X^10
def certI12 : P := X + X^2 + X^3 + X^5 + X^9
def certQ12 : P := 1 + X + X^2 + X^3 + X^4 + X^5 + X^8
lemma certInvPoly12 : certV12 * certI12 + 1 = f * certQ12 := by
  unfold certV12 certI12 certQ12 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV13 : P := X + X^3 + X^5 + X^7 + X^10
def certI13 : P := X + X^3 + X^6 + X^7 + X^8 + X^9 + X^10
def certQ13 : P := 1 + X^7 + X^8 + X^9
lemma certInvPoly13 : certV13 * certI13 + 1 = f * certQ13 := by
  unfold certV13 certI13 certQ13 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV14 : P := 1 + X + X^3 + X^4 + X^7 + X^8 + X^9
def certI14 : P := X^2 + X^3 + X^8
def certQ14 : P := 1 + X^4 + X^5 + X^6
lemma certInvPoly14 : certV14 * certI14 + 1 = f * certQ14 := by
  unfold certV14 certI14 certQ14 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV15 : P := X + X^3 + X^4 + X^7 + X^8 + X^9
def certI15 : P := 1 + X + X^4 + X^5 + X^7 + X^8
def certQ15 : P := 1 + X + X^6
lemma certInvPoly15 : certV15 * certI15 + 1 = f * certQ15 := by
  unfold certV15 certI15 certQ15 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV16 : P := 1 + X^2 + X^3 + X^4 + X^5 + X^9 + X^10
def certI16 : P := 1 + X^2 + X^3 + X^4 + X^6 + X^8 + X^9
def certQ16 : P := X^4 + X^5 + X^6 + X^8
lemma certInvPoly16 : certV16 * certI16 + 1 = f * certQ16 := by
  unfold certV16 certI16 certQ16 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV17 : P := X^2 + X^3 + X^4 + X^5 + X^9 + X^10
def certI17 : P := X^2 + X^6 + X^8 + X^9 + X^10
def certQ17 : P := 1 + X^2 + X^5 + X^6 + X^9
lemma certInvPoly17 : certV17 * certI17 + 1 = f * certQ17 := by
  unfold certV17 certI17 certQ17 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV18 : P := 1 + X^2 + X^3 + X^8
def certI18 : P := X + X^4 + X^5 + X^7 + X^8
def certQ18 : P := 1 + X + X^2 + X^4 + X^5
lemma certInvPoly18 : certV18 * certI18 + 1 = f * certQ18 := by
  unfold certV18 certI18 certQ18 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV19 : P := X^2 + X^3 + X^8
def certI19 : P := 1 + X + X^3 + X^4 + X^7 + X^8 + X^9
def certQ19 : P := 1 + X^4 + X^5 + X^6
lemma certInvPoly19 : certV19 * certI19 + 1 = f * certQ19 := by
  unfold certV19 certI19 certQ19 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV20 : P := 1 + X + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9
def certI20 : P := 1 + X^2 + X^3 + X^5 + X^6 + X^8 + X^9
def certQ20 : P := X + X^4 + X^7
lemma certInvPoly20 : certV20 * certI20 + 1 = f * certQ20 := by
  unfold certV20 certI20 certQ20 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV21 : P := X + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9
def certI21 : P := X + X^2
def certQ21 : P := 1
lemma certInvPoly21 : certV21 * certI21 + 1 = f * certQ21 := by
  unfold certV21 certI21 certQ21 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV22 : P := 1 + X + X^2 + X^3 + X^6 + X^7 + X^10
def certI22 : P := 1 + X + X^2 + X^4 + X^5 + X^7 + X^8
def certQ22 : P := X^2 + X^3 + X^6 + X^7
lemma certInvPoly22 : certV22 * certI22 + 1 = f * certQ22 := by
  unfold certV22 certI22 certQ22 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV23 : P := X + X^2 + X^3 + X^6 + X^7 + X^10
def certI23 : P := 1 + X + X^2 + X^3
def certQ23 : P := 1 + X + X^2
lemma certInvPoly23 : certV23 * certI23 + 1 = f * certQ23 := by
  unfold certV23 certI23 certQ23 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV24 : P := X^2 + X^4 + X^6 + X^8 + X^9 + X^10
def certI24 : P := X + X^2 + X^3 + X^5 + X^7
def certQ24 : P := 1 + X^2 + X^3 + X^5 + X^6
lemma certInvPoly24 : certV24 * certI24 + 1 = f * certQ24 := by
  unfold certV24 certI24 certQ24 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV25 : P := 1 + X^2 + X^4 + X^6 + X^8 + X^9 + X^10
def certI25 : P := 1 + X^4 + X^6 + X^7 + X^9
def certQ25 : P := X^2 + X^4 + X^7 + X^8
lemma certInvPoly25 : certV25 * certI25 + 1 = f * certQ25 := by
  unfold certV25 certI25 certQ25 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV26 : P := X^2 + X^5 + X^6
def certI26 : P := 1 + X^2 + X^6 + X^10
def certQ26 : P := 1 + X^4 + X^5
lemma certInvPoly26 : certV26 * certI26 + 1 = f * certQ26 := by
  unfold certV26 certI26 certQ26 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV27 : P := 1 + X^2 + X^5 + X^6
def certI27 : P := X^4 + X^5 + X^6 + X^8 + X^9 + X^10
def certQ27 : P := 1 + X^2 + X^5
lemma certInvPoly27 : certV27 * certI27 + 1 = f * certQ27 := by
  unfold certV27 certI27 certQ27 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV28 : P := X + X^2 + X^4 + X^7 + X^9
def certI28 : P := 1 + X + X^2 + X^4 + X^7 + X^8
def certQ28 : P := 1 + X + X^2 + X^3 + X^4 + X^5 + X^6
lemma certInvPoly28 : certV28 * certI28 + 1 = f * certQ28 := by
  unfold certV28 certI28 certQ28 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV29 : P := 1 + X + X^2 + X^4 + X^7 + X^9
def certI29 : P := X + X^2 + X^3 + X^4 + X^5 + X^10
def certQ29 : P := 1 + X + X^2 + X^6 + X^8
lemma certInvPoly29 : certV29 * certI29 + 1 = f * certQ29 := by
  unfold certV29 certI29 certQ29 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV30 : P := X + X^2 + X^5 + X^7 + X^8 + X^10
def certI30 : P := 1 + X + X^4 + X^8 + X^9
def certQ30 : P := 1 + X + X^2 + X^4 + X^6 + X^7 + X^8
lemma certInvPoly30 : certV30 * certI30 + 1 = f * certQ30 := by
  unfold certV30 certI30 certQ30 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
def certV31 : P := 1 + X + X^2 + X^5 + X^7 + X^8 + X^10
def certI31 : P := X + X^3 + X^5 + X^9
def certQ31 : P := 1 + X + X^3 + X^4 + X^5 + X^6 + X^8
lemma certInvPoly31 : certV31 * certI31 + 1 = f * certQ31 := by
  unfold certV31 certI31 certQ31 f
  ring_nf
  simp [c2,c3,c4,c5,c6,c7,c8]
theorem cert_inverse_representatives_sum : certI01 + certI02 + certI03 + certI04 + certI05 + certI06 + certI07 + certI08 + certI09 + certI10 + certI11 + certI12 + certI13 + certI14 + certI15 + certI16 + certI17 + certI18 + certI19 + certI20 + certI21 + certI22 + certI23 + certI24 + certI25 + certI26 + certI27 + certI28 + certI29 + certI30 + certI31 = 0 := by
  unfold certI01 certI02 certI03 certI04 certI05 certI06 certI07 certI08 certI09 certI10 certI11 certI12 certI13 certI14 certI15 certI16 certI17 certI18 certI19 certI20 certI21 certI22 certI23 certI24 certI25 certI26 certI27 certI28 certI29 certI30 certI31
  ring_nf
  have hc10 : (10 : P) = 0 := by change Polynomial.C ((10:Nat):F)=0; rw [natCast_mod_two]; norm_num
  have hc12 : (12 : P) = 0 := by change Polynomial.C ((12:Nat):F)=0; rw [natCast_mod_two]; norm_num
  have hc14 : (14 : P) = 0 := by change Polynomial.C ((14:Nat):F)=0; rw [natCast_mod_two]; norm_num
  have hc16 : (16 : P) = 0 := by change Polynomial.C ((16:Nat):F)=0; rw [natCast_mod_two]; norm_num
  have hc18 : (18 : P) = 0 := by change Polynomial.C ((18:Nat):F)=0; rw [natCast_mod_two]; norm_num
  have hc20 : (20 : P) = 0 := by change Polynomial.C ((20:Nat):F)=0; rw [natCast_mod_two]; norm_num
  simp only [hc10,hc12,hc14,hc16,hc18,hc20,zero_mul,mul_zero,add_zero,zero_add]
#print axioms cert_inverse_representatives_sum


local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
abbrev L := AdjoinRoot f
local instance : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
theorem certInvAdjoin01 : (AdjoinRoot.mk f certV01) * (AdjoinRoot.mk f certI01) = 1 := by
  have hd : f ∣ certV01 * certI01 + 1 := ⟨certQ01, certInvPoly01⟩
  have hz : AdjoinRoot.mk f (certV01 * certI01 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV01) * (AdjoinRoot.mk f certI01) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV01) * (AdjoinRoot.mk f certI01) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin02 : (AdjoinRoot.mk f certV02) * (AdjoinRoot.mk f certI02) = 1 := by
  have hd : f ∣ certV02 * certI02 + 1 := ⟨certQ02, certInvPoly02⟩
  have hz : AdjoinRoot.mk f (certV02 * certI02 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV02) * (AdjoinRoot.mk f certI02) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV02) * (AdjoinRoot.mk f certI02) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin03 : (AdjoinRoot.mk f certV03) * (AdjoinRoot.mk f certI03) = 1 := by
  have hd : f ∣ certV03 * certI03 + 1 := ⟨certQ03, certInvPoly03⟩
  have hz : AdjoinRoot.mk f (certV03 * certI03 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV03) * (AdjoinRoot.mk f certI03) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV03) * (AdjoinRoot.mk f certI03) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin04 : (AdjoinRoot.mk f certV04) * (AdjoinRoot.mk f certI04) = 1 := by
  have hd : f ∣ certV04 * certI04 + 1 := ⟨certQ04, certInvPoly04⟩
  have hz : AdjoinRoot.mk f (certV04 * certI04 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV04) * (AdjoinRoot.mk f certI04) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV04) * (AdjoinRoot.mk f certI04) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin05 : (AdjoinRoot.mk f certV05) * (AdjoinRoot.mk f certI05) = 1 := by
  have hd : f ∣ certV05 * certI05 + 1 := ⟨certQ05, certInvPoly05⟩
  have hz : AdjoinRoot.mk f (certV05 * certI05 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV05) * (AdjoinRoot.mk f certI05) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV05) * (AdjoinRoot.mk f certI05) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin06 : (AdjoinRoot.mk f certV06) * (AdjoinRoot.mk f certI06) = 1 := by
  have hd : f ∣ certV06 * certI06 + 1 := ⟨certQ06, certInvPoly06⟩
  have hz : AdjoinRoot.mk f (certV06 * certI06 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV06) * (AdjoinRoot.mk f certI06) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV06) * (AdjoinRoot.mk f certI06) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin07 : (AdjoinRoot.mk f certV07) * (AdjoinRoot.mk f certI07) = 1 := by
  have hd : f ∣ certV07 * certI07 + 1 := ⟨certQ07, certInvPoly07⟩
  have hz : AdjoinRoot.mk f (certV07 * certI07 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV07) * (AdjoinRoot.mk f certI07) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV07) * (AdjoinRoot.mk f certI07) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin08 : (AdjoinRoot.mk f certV08) * (AdjoinRoot.mk f certI08) = 1 := by
  have hd : f ∣ certV08 * certI08 + 1 := ⟨certQ08, certInvPoly08⟩
  have hz : AdjoinRoot.mk f (certV08 * certI08 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV08) * (AdjoinRoot.mk f certI08) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV08) * (AdjoinRoot.mk f certI08) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin09 : (AdjoinRoot.mk f certV09) * (AdjoinRoot.mk f certI09) = 1 := by
  have hd : f ∣ certV09 * certI09 + 1 := ⟨certQ09, certInvPoly09⟩
  have hz : AdjoinRoot.mk f (certV09 * certI09 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV09) * (AdjoinRoot.mk f certI09) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV09) * (AdjoinRoot.mk f certI09) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin10 : (AdjoinRoot.mk f certV10) * (AdjoinRoot.mk f certI10) = 1 := by
  have hd : f ∣ certV10 * certI10 + 1 := ⟨certQ10, certInvPoly10⟩
  have hz : AdjoinRoot.mk f (certV10 * certI10 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV10) * (AdjoinRoot.mk f certI10) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV10) * (AdjoinRoot.mk f certI10) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin11 : (AdjoinRoot.mk f certV11) * (AdjoinRoot.mk f certI11) = 1 := by
  have hd : f ∣ certV11 * certI11 + 1 := ⟨certQ11, certInvPoly11⟩
  have hz : AdjoinRoot.mk f (certV11 * certI11 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV11) * (AdjoinRoot.mk f certI11) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV11) * (AdjoinRoot.mk f certI11) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin12 : (AdjoinRoot.mk f certV12) * (AdjoinRoot.mk f certI12) = 1 := by
  have hd : f ∣ certV12 * certI12 + 1 := ⟨certQ12, certInvPoly12⟩
  have hz : AdjoinRoot.mk f (certV12 * certI12 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV12) * (AdjoinRoot.mk f certI12) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV12) * (AdjoinRoot.mk f certI12) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin13 : (AdjoinRoot.mk f certV13) * (AdjoinRoot.mk f certI13) = 1 := by
  have hd : f ∣ certV13 * certI13 + 1 := ⟨certQ13, certInvPoly13⟩
  have hz : AdjoinRoot.mk f (certV13 * certI13 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV13) * (AdjoinRoot.mk f certI13) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV13) * (AdjoinRoot.mk f certI13) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin14 : (AdjoinRoot.mk f certV14) * (AdjoinRoot.mk f certI14) = 1 := by
  have hd : f ∣ certV14 * certI14 + 1 := ⟨certQ14, certInvPoly14⟩
  have hz : AdjoinRoot.mk f (certV14 * certI14 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV14) * (AdjoinRoot.mk f certI14) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV14) * (AdjoinRoot.mk f certI14) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin15 : (AdjoinRoot.mk f certV15) * (AdjoinRoot.mk f certI15) = 1 := by
  have hd : f ∣ certV15 * certI15 + 1 := ⟨certQ15, certInvPoly15⟩
  have hz : AdjoinRoot.mk f (certV15 * certI15 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV15) * (AdjoinRoot.mk f certI15) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV15) * (AdjoinRoot.mk f certI15) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin16 : (AdjoinRoot.mk f certV16) * (AdjoinRoot.mk f certI16) = 1 := by
  have hd : f ∣ certV16 * certI16 + 1 := ⟨certQ16, certInvPoly16⟩
  have hz : AdjoinRoot.mk f (certV16 * certI16 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV16) * (AdjoinRoot.mk f certI16) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV16) * (AdjoinRoot.mk f certI16) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin17 : (AdjoinRoot.mk f certV17) * (AdjoinRoot.mk f certI17) = 1 := by
  have hd : f ∣ certV17 * certI17 + 1 := ⟨certQ17, certInvPoly17⟩
  have hz : AdjoinRoot.mk f (certV17 * certI17 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV17) * (AdjoinRoot.mk f certI17) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV17) * (AdjoinRoot.mk f certI17) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin18 : (AdjoinRoot.mk f certV18) * (AdjoinRoot.mk f certI18) = 1 := by
  have hd : f ∣ certV18 * certI18 + 1 := ⟨certQ18, certInvPoly18⟩
  have hz : AdjoinRoot.mk f (certV18 * certI18 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV18) * (AdjoinRoot.mk f certI18) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV18) * (AdjoinRoot.mk f certI18) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin19 : (AdjoinRoot.mk f certV19) * (AdjoinRoot.mk f certI19) = 1 := by
  have hd : f ∣ certV19 * certI19 + 1 := ⟨certQ19, certInvPoly19⟩
  have hz : AdjoinRoot.mk f (certV19 * certI19 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV19) * (AdjoinRoot.mk f certI19) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV19) * (AdjoinRoot.mk f certI19) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin20 : (AdjoinRoot.mk f certV20) * (AdjoinRoot.mk f certI20) = 1 := by
  have hd : f ∣ certV20 * certI20 + 1 := ⟨certQ20, certInvPoly20⟩
  have hz : AdjoinRoot.mk f (certV20 * certI20 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV20) * (AdjoinRoot.mk f certI20) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV20) * (AdjoinRoot.mk f certI20) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin21 : (AdjoinRoot.mk f certV21) * (AdjoinRoot.mk f certI21) = 1 := by
  have hd : f ∣ certV21 * certI21 + 1 := ⟨certQ21, certInvPoly21⟩
  have hz : AdjoinRoot.mk f (certV21 * certI21 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV21) * (AdjoinRoot.mk f certI21) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV21) * (AdjoinRoot.mk f certI21) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin22 : (AdjoinRoot.mk f certV22) * (AdjoinRoot.mk f certI22) = 1 := by
  have hd : f ∣ certV22 * certI22 + 1 := ⟨certQ22, certInvPoly22⟩
  have hz : AdjoinRoot.mk f (certV22 * certI22 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV22) * (AdjoinRoot.mk f certI22) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV22) * (AdjoinRoot.mk f certI22) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin23 : (AdjoinRoot.mk f certV23) * (AdjoinRoot.mk f certI23) = 1 := by
  have hd : f ∣ certV23 * certI23 + 1 := ⟨certQ23, certInvPoly23⟩
  have hz : AdjoinRoot.mk f (certV23 * certI23 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV23) * (AdjoinRoot.mk f certI23) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV23) * (AdjoinRoot.mk f certI23) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin24 : (AdjoinRoot.mk f certV24) * (AdjoinRoot.mk f certI24) = 1 := by
  have hd : f ∣ certV24 * certI24 + 1 := ⟨certQ24, certInvPoly24⟩
  have hz : AdjoinRoot.mk f (certV24 * certI24 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV24) * (AdjoinRoot.mk f certI24) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV24) * (AdjoinRoot.mk f certI24) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin25 : (AdjoinRoot.mk f certV25) * (AdjoinRoot.mk f certI25) = 1 := by
  have hd : f ∣ certV25 * certI25 + 1 := ⟨certQ25, certInvPoly25⟩
  have hz : AdjoinRoot.mk f (certV25 * certI25 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV25) * (AdjoinRoot.mk f certI25) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV25) * (AdjoinRoot.mk f certI25) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin26 : (AdjoinRoot.mk f certV26) * (AdjoinRoot.mk f certI26) = 1 := by
  have hd : f ∣ certV26 * certI26 + 1 := ⟨certQ26, certInvPoly26⟩
  have hz : AdjoinRoot.mk f (certV26 * certI26 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV26) * (AdjoinRoot.mk f certI26) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV26) * (AdjoinRoot.mk f certI26) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin27 : (AdjoinRoot.mk f certV27) * (AdjoinRoot.mk f certI27) = 1 := by
  have hd : f ∣ certV27 * certI27 + 1 := ⟨certQ27, certInvPoly27⟩
  have hz : AdjoinRoot.mk f (certV27 * certI27 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV27) * (AdjoinRoot.mk f certI27) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV27) * (AdjoinRoot.mk f certI27) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin28 : (AdjoinRoot.mk f certV28) * (AdjoinRoot.mk f certI28) = 1 := by
  have hd : f ∣ certV28 * certI28 + 1 := ⟨certQ28, certInvPoly28⟩
  have hz : AdjoinRoot.mk f (certV28 * certI28 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV28) * (AdjoinRoot.mk f certI28) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV28) * (AdjoinRoot.mk f certI28) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin29 : (AdjoinRoot.mk f certV29) * (AdjoinRoot.mk f certI29) = 1 := by
  have hd : f ∣ certV29 * certI29 + 1 := ⟨certQ29, certInvPoly29⟩
  have hz : AdjoinRoot.mk f (certV29 * certI29 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV29) * (AdjoinRoot.mk f certI29) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV29) * (AdjoinRoot.mk f certI29) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin30 : (AdjoinRoot.mk f certV30) * (AdjoinRoot.mk f certI30) = 1 := by
  have hd : f ∣ certV30 * certI30 + 1 := ⟨certQ30, certInvPoly30⟩
  have hz : AdjoinRoot.mk f (certV30 * certI30 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV30) * (AdjoinRoot.mk f certI30) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV30) * (AdjoinRoot.mk f certI30) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht
theorem certInvAdjoin31 : (AdjoinRoot.mk f certV31) * (AdjoinRoot.mk f certI31) = 1 := by
  have hd : f ∣ certV31 * certI31 + 1 := ⟨certQ31, certInvPoly31⟩
  have hz : AdjoinRoot.mk f (certV31 * certI31 + 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hd
  have hm : (AdjoinRoot.mk f certV31) * (AdjoinRoot.mk f certI31) + 1 = 0 := by simpa only [map_add, map_mul, map_one] using hz
  calc
    (AdjoinRoot.mk f certV31) * (AdjoinRoot.mk f certI31) = -1 := eq_neg_of_add_eq_zero_left hm
    _ = 1 := by
      have ht : (1 : L) + 1 = 0 := by
        calc
          (1 : L) + 1 = (2 : L) := by norm_num
          _ = 0 := CharP.cast_eq_zero L 2
      exact neg_eq_of_add_eq_zero_left ht

theorem cert_inverse_sum_adjoin : AdjoinRoot.mk f certI01 + AdjoinRoot.mk f certI02 + AdjoinRoot.mk f certI03 + AdjoinRoot.mk f certI04 + AdjoinRoot.mk f certI05 + AdjoinRoot.mk f certI06 + AdjoinRoot.mk f certI07 + AdjoinRoot.mk f certI08 + AdjoinRoot.mk f certI09 + AdjoinRoot.mk f certI10 + AdjoinRoot.mk f certI11 + AdjoinRoot.mk f certI12 + AdjoinRoot.mk f certI13 + AdjoinRoot.mk f certI14 + AdjoinRoot.mk f certI15 + AdjoinRoot.mk f certI16 + AdjoinRoot.mk f certI17 + AdjoinRoot.mk f certI18 + AdjoinRoot.mk f certI19 + AdjoinRoot.mk f certI20 + AdjoinRoot.mk f certI21 + AdjoinRoot.mk f certI22 + AdjoinRoot.mk f certI23 + AdjoinRoot.mk f certI24 + AdjoinRoot.mk f certI25 + AdjoinRoot.mk f certI26 + AdjoinRoot.mk f certI27 + AdjoinRoot.mk f certI28 + AdjoinRoot.mk f certI29 + AdjoinRoot.mk f certI30 + AdjoinRoot.mk f certI31 = 0 := by
  have h := congrArg (AdjoinRoot.mk f) cert_inverse_representatives_sum
  simpa only [map_add, map_zero] using h
#print axioms cert_inverse_sum_adjoin


