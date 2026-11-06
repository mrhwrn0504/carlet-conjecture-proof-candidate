/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.ChordExpansion
import HasseWeil.Foundation.EC.MulByIntAddRecurrence
import HasseWeil.Isogeny.FormalSeries
import HasseWeil.Foundation.Ramification
import HasseWeil.Foundation.OmegaCoeffMulByIntFiniteField
import HasseWeil.Foundation.Curves.Valuation.Infinity
import HasseWeil.Foundation.Curves.Map.CurveMapBaseChange
import HasseWeil.Foundation.EC.DifferentialOrd
import HasseWeil.Foundation.EC.TranslateOrdInfty

/-!
# GAP-QF kernel: `omegaPullbackCoeff (mulByInt m) = m` via the formal group

The irreducible kernel of the Hasse degree-quadratic-form (`a_{[m]} = m`), built Silverman's
formal-group way (Chapter IV). Each statement is cross-checked against the Silverman text
(read 2026-05-22, not proof-length-guessed):

* **L-F1** `coeff_one_formalIsogenySeries_mulByInt_eq` — Silverman IV.2.3a (`[m]_F(T)=mT+…`,
  `m ≠ 0`; the `m = 0` junk-pullback instance is false, see
  `coeff_one_formalIsogenySeries_mulByInt_zero`). **PROVEN, axiom-clean** (2026-06-11):
  the BRIDGE-003 instance `formalIsogenySeries_FGL_additivity` is discharged from the
  general pair theorem `formalIsogenySeries_add` (`ChordExpansion.lean`) via the
  `[k] ⊞ [1] = [k+1]` identification (`addPullback_xy_pair_mulByInt_one_eq_succ`,
  `EC/MulByIntAddRecurrence.lean`); the negative case is the (axiom-clean) negation step
  `coeff_one_formalIsogenySeries_mulByInt_neg_eq`.
* **L-KL.1** `localExpand_derivative_leibniz` — Silverman IV.1: the local expansion respects
  `d/dz`; the composite `f ↦ (d/dz)(localExpand f)` is a derivation.
* **L-KL-main** `omegaPullbackCoeff_localExpand_eq_coeff_one` — Silverman IV.1 + IV.4.3
  (`FormalGroup.invariantDiff_chain`): localizing `φ*ω = a_φ·ω` forces `localExpand(a_φ)` to be
  the constant `coeff 1 (formalIsogenySeries α)`. (Avoids `div(ω)=0` via injectivity of
  `localExpand`, in place of the III.5.6 divisor argument.)
* **BRIDGE-001** `omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization` — discharges the
  curve↔formal bridge from L-KL-main + `localExpand` injectivity.
* **TOP** `omegaPullbackCoeff_mulByInt_via_formalGroup` — Silverman III.5.3 (`[m]*ω = m·ω`,
  `m ≠ 0`), obtained through the formal group. The coefficient is constant by the proved
  integrality and infinity-regularity theorems; the x-pole chart and normalized invariant
  differential identify that constant with the linear coefficient of the formal series.

Full decomposition + fillability: `.mathlib-quality/GAP-QF-KERNEL-SKELETON.md`.
-/

open WeierstrassCurve PowerSeries

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- `[n]^* t = -mulByInt_x n / mulByInt_y n` for `n ≠ 0`: the pullback of the local
parameter `t = -x/y` in division-polynomial coordinates. -/
theorem mulByInt_pullback_localParam (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).pullback (localParam W) =
      -mulByInt_x W n / mulByInt_y W n := by
  rw [localParam, map_div₀, map_neg,
    show (mulByInt W.toAffine n).pullback (x_gen W) = mulByInt_x W n from
      mulByInt_pullback_x W n hn,
    show (mulByInt W.toAffine n).pullback (y_gen W) = mulByInt_y W n from
      mulByInt_pullback_y W n hn]

/-- **BRIDGE-003 instance** (Silverman IV.2.3a substance): the formal isogeny series of `[k+1]`
is the formal-group-law sum of the series of `[k]` and `[1]` — `[k+1]_F = F([k]_F, [1]_F)`. This
is the substantive content from which `coeff 1 [n] = n` follows by the shipped induction closer
`coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`.

**PROVEN (FG-C2)** by instantiating the general pair theorem `formalIsogenySeries_add`
(`ChordExpansion.lean`, T-IV-BRIDGE-003) at `(α, β) = ([k], [1])`: the chord/tangent sum of
`[k]·P_gen` and `[1]·P_gen` *is* `[k+1]·P_gen` (Silverman III.4.2 via `zsmul_genericPoint_eq`
and mathlib's `add_of_X_ne`/`add_self_of_Y_ne`), so the pair sum's `z`-expansion is
`localExpand ([k+1]^* t) = ofPowerSeries [k+1]_F`, and `ofPowerSeries`-injectivity descends
the Laurent identity to `PowerSeries`. The `k = 1` instance takes the tangent branch
(`mulByInt_y_one_ne_negY` supplies both the non-inverse hypothesis and the `Y ≠ negY` slope
guard); `k ≥ 2` takes the chord branch (`mulByInt_x_ne_mulByInt_x`). -/
theorem formalIsogenySeries_FGL_additivity :
    ∀ k : ℕ, 1 ≤ k →
      formalIsogenySeries W (mulByInt W.toAffine ((k : ℤ) + 1)) =
        MvPowerSeries.subst
          (![formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)),
             formalIsogenySeries W (mulByInt W.toAffine 1)] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries := by
  intro k hk
  have hk1' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hk0 : (k : ℤ) ≠ 0 := by omega
  have hk10 : ((k : ℤ) + 1) ≠ 0 := by omega
  -- The pole hypotheses for the pair theorem.
  have h_α : (W_smooth W).ordAtInfty ((mulByInt W.toAffine (k : ℤ)).pullback (x_gen W)) < 0 := by
    rw [show (mulByInt W.toAffine (k : ℤ)).pullback (x_gen W) = mulByInt_x W (k : ℤ) from
      mulByInt_pullback_x W _ hk0]
    exact ordAtInfty_mulByInt_x_neg W _ hk0
  have h_β : (W_smooth W).ordAtInfty ((mulByInt W.toAffine 1).pullback (x_gen W)) < 0 := by
    rw [show (mulByInt W.toAffine 1).pullback (x_gen W) = mulByInt_x W 1 from
      mulByInt_pullback_x W 1 one_ne_zero]
    exact ordAtInfty_mulByInt_x_neg W 1 one_ne_zero
  -- BRIDGE-003 (the pair theorem) at `([k], [1])`; non-inverseness is the
  -- chord/tangent dichotomy `addNonInversePair_mulByInt_one`.
  have h_iv14 := formalIsogenySeries_add W (mulByInt W.toAffine (k : ℤ))
    (mulByInt W.toAffine 1) h_α h_β (addNonInversePair_mulByInt_one W (k : ℤ) hk0 hk10)
  -- The chord-sum coordinates are `[k+1]`'s division-polynomial coordinates
  -- (`[k] ⊞ [1] = [k+1]`, Silverman III.5.3, pair order).
  obtain ⟨hX_id, hY_id⟩ := addPullback_xy_pair_mulByInt_one_eq_succ W (k : ℤ) hk0 hk10
  -- The pair sum's `z`-expansion is `ofPowerSeries [k+1]_F`.
  have h_pole_k1 : (W_smooth W).ordAtInfty
      ((mulByInt W.toAffine ((k : ℤ) + 1)).pullback (x_gen W)) < 0 := by
    rw [show (mulByInt W.toAffine ((k : ℤ) + 1)).pullback (x_gen W)
        = mulByInt_x W ((k : ℤ) + 1) from mulByInt_pullback_x W _ hk10]
    exact ordAtInfty_mulByInt_x_neg W _ hk10
  have hL : localExpand W
      (-(addPullback_x_pair (mulByInt W.toAffine (k : ℤ)) (mulByInt W.toAffine 1))
        / (addPullback_y_pair (mulByInt W.toAffine (k : ℤ)) (mulByInt W.toAffine 1))) =
      HahnSeries.ofPowerSeries ℤ F
        (formalIsogenySeries W (mulByInt W.toAffine ((k : ℤ) + 1))) := by
    rw [hX_id, hY_id, ← mulByInt_pullback_localParam W _ hk10]
    exact localExpand_pullback_localParam W _ h_pole_k1
  -- Descend the Laurent identity along the injective `ofPowerSeries`.
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F)
  rw [← hL]
  exact h_iv14

/-! ### L-F1 sub-leaf: ℤ→ℕ negation/zero extension (IV.2.3a, `m ≤ 0`)

**B2 restatement (2026-06-11)**: the original leaf claimed `coeff 1 [m]_F = m` for all `m ≤ 0`,
but the `m = 0` instance is FALSE for the project's `mulByInt`: the `[0]` branch carries the
junk pullback `AlgHom.id` (see `mulByInt`, `Basic.lean` — `[0]` is not an isogeny and has no
finite comorphism), so `formalIsogenySeries W (mulByInt 0) = X` and `coeff 1 = 1 ≠ 0`. The
counterexample is machine-checked below (`coeff_one_formalIsogenySeries_mulByInt_zero`); the
leaf is restated with the honest `m < 0` guard, and the combined IV.2.3a statement
`coeff_one_formalIsogenySeries_mulByInt_eq` now carries `m ≠ 0` (matching every degree-style
`mulByInt` theorem in the project).

The `m < 0` case is the negation step `[−n]_F(T) = i_F([n]_F(T))` at the linear coefficient:
`coeff 1 [−n]_F = −coeff 1 [n]_F` is proved *series-level and axiom-clean*
(`coeff_one_formalIsogenySeries_mulByInt_neg_eq` below) from the division-polynomial negation
formulas (`mulByInt_x_neg`/`mulByInt_y_neg`) and a Laurent-coefficient extraction; the positive
case is the BRIDGE-003 induction closer fed by `formalIsogenySeries_FGL_additivity`
(proven above, 2026-06-11) — the whole IV.2.3a family is axiom-clean. -/

/-- **The `m = 0` junk value**: `formalIsogenySeries W (mulByInt 0) = X`. The `[0]` branch of
`mulByInt` carries the junk pullback `AlgHom.id` (`[0]` is not an isogeny; see `mulByInt`), so
its formal series is the expansion of `localParam` itself. -/
theorem formalIsogenySeries_mulByInt_zero :
    formalIsogenySeries W (mulByInt W.toAffine 0) = PowerSeries.X := by
  have h_pb : (mulByInt W.toAffine 0).pullback = AlgHom.id F W.toAffine.FunctionField := by
    unfold mulByInt
    dsimp only
    exact dif_pos rfl
  ext n
  rw [formalIsogenySeries_coeff, h_pb, AlgHom.id_apply, localExpand_localParam,
    PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst hn
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from rfl, HahnSeries.coeff_single_same, if_pos rfl]
  · have hn' : (n : ℤ) ≠ (1 : ℤ) := by exact_mod_cast hn
    rw [HahnSeries.coeff_single_of_ne hn', if_neg hn]

/-- The machine-checked counterexample to the unguarded IV.2.3a at `m = 0`:
`coeff 1 (formalIsogenySeries W (mulByInt 0)) = 1`, not `0`. This is why
`coeff_one_formalIsogenySeries_mulByInt_eq` carries the `m ≠ 0` guard. -/
theorem coeff_one_formalIsogenySeries_mulByInt_zero :
    PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine 0)) = 1 := by
  rw [formalIsogenySeries_mulByInt_zero, PowerSeries.coeff_X, if_pos rfl]

omit [DecidableEq F] in
/-- `mulByInt_y W (-n)` in explicit curve-negation form: `[-n]^* y = -[n]^* y - a₁·[n]^* x - a₃`
(`mulByInt_y_neg` with `negY` unfolded). -/
theorem mulByInt_y_neg_explicit (n : ℤ) (hn : n ≠ 0) :
    mulByInt_y W (-n) =
      -mulByInt_y W n - algebraMap F KE W.a₁ * mulByInt_x W n - algebraMap F KE W.a₃ := by
  rw [mulByInt_y_neg W n hn]
  rfl

/-- **IV.2.3a negation step (series level, axiom-clean)**: the linear coefficient of the
formal isogeny series negates under `n ↦ -n`. This is `[−n]_F = i_F ∘ [n]_F` read off at the
linear coefficient (`coeff 1 i_F = −1`), but proved without substitution machinery: with
`s := localExpand ([n]^* t)`, `s' := localExpand ([−n]^* t)`, `A := localExpand ([n]^* x)`,
`B := localExpand ([n]^* y)`, the division-polynomial negation formulas give the pole
relations `B·s = −A` and `(−B − a₁A − a₃)·s' = −A`, whence the Laurent identity
`s' + s = s'·(a₁·s − a₃·B⁻¹)`. The right side is a product of two series of `orderTop ≥ 1`
(genuineness of `[±n]` + `orderTop B ≤ −1` from the `x`-pole), so its coefficient at `1`
vanishes, giving `s'₁ = −s₁`. -/
theorem coeff_one_formalIsogenySeries_mulByInt_neg_eq (n : ℤ) (hn : n ≠ 0) :
    PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine (-n))) =
      -PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine n)) := by
  classical
  have hn' : (-n : ℤ) ≠ 0 := neg_ne_zero.mpr hn
  have hX_ne : mulByInt_x W n ≠ 0 := mulByInt_x_ne_zero W n hn
  have hY_ne : mulByInt_y W n ≠ 0 := mulByInt_y_ne_zero W n hn
  have hYneg_ne : -mulByInt_y W n - algebraMap F KE W.a₁ * mulByInt_x W n -
      algebraMap F KE W.a₃ ≠ 0 := by
    rw [← mulByInt_y_neg_explicit W n hn]
    exact mulByInt_y_ne_zero W (-n) hn'
  -- the two pullbacks of the local parameter
  have ht_n : (mulByInt W.toAffine n).pullback (localParam W) =
      -mulByInt_x W n / mulByInt_y W n := mulByInt_pullback_localParam W n hn
  have ht_neg : (mulByInt W.toAffine (-n)).pullback (localParam W) =
      -mulByInt_x W n / (-mulByInt_y W n - algebraMap F KE W.a₁ * mulByInt_x W n -
        algebraMap F KE W.a₃) := by
    rw [mulByInt_pullback_localParam W (-n) hn', mulByInt_x_neg, mulByInt_y_neg_explicit W n hn]
  -- division-free pole relations at the KE level
  have hKE1 : mulByInt_y W n * ((mulByInt W.toAffine n).pullback (localParam W)) =
      -mulByInt_x W n := by
    rw [ht_n]
    field_simp
  have hKE2 : (-mulByInt_y W n - algebraMap F KE W.a₁ * mulByInt_x W n -
        algebraMap F KE W.a₃) * ((mulByInt W.toAffine (-n)).pullback (localParam W)) =
      -mulByInt_x W n := by
    rw [ht_neg]
    field_simp
  -- Laurent-side abbreviations
  set s : LaurentSeries F :=
    localExpand W ((mulByInt W.toAffine n).pullback (localParam W)) with hs_def
  set s' : LaurentSeries F :=
    localExpand W ((mulByInt W.toAffine (-n)).pullback (localParam W)) with hs'_def
  set A : LaurentSeries F := localExpand W (mulByInt_x W n) with hA_def
  set B : LaurentSeries F := localExpand W (mulByInt_y W n) with hB_def
  have hca : ∀ a : F, localExpand W (algebraMap F KE a) = HahnSeries.single (0 : ℤ) a := by
    intro a
    rw [localExpand_algebraMap, HahnSeries.ofPowerSeries_C]
    rfl
  -- transported pole relations
  have hP1 : B * s = -A := by
    rw [hB_def, hs_def, hA_def, ← map_neg, ← map_mul]
    exact congrArg (localExpand W) hKE1
  have hP2 : (-B - HahnSeries.single (0 : ℤ) W.a₁ * A - HahnSeries.single (0 : ℤ) W.a₃) * s' =
      -A := by
    rw [hB_def, hs'_def, hA_def, ← hca, ← hca, ← map_neg, ← map_mul, ← map_sub, ← map_sub,
      ← map_mul, ← map_neg]
    exact congrArg (localExpand W) hKE2
  -- nonvanishing on the Laurent side (`localExpand_injective` is declared below, so use
  -- the underlying `RingHom.injective` directly)
  have hA_ne : A ≠ 0 := by
    rw [hA_def]
    intro h
    exact hX_ne ((localExpand W).injective (by rw [h, map_zero]))
  have hB_ne : B ≠ 0 := by
    rw [hB_def]
    intro h
    exact hY_ne ((localExpand W).injective (by rw [h, map_zero]))
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hP1
    exact hA_ne (neg_eq_zero.mp hP1.symm)
  -- the Laurent-side identity s' + s = s'·(a₁·s − a₃·B⁻¹)
  have hL : s' + s = s' * (HahnSeries.single (0 : ℤ) W.a₁ * s -
      HahnSeries.single (0 : ℤ) W.a₃ * B⁻¹) := by
    field_simp
    linear_combination (1 - HahnSeries.single (0 : ℤ) W.a₁ * s') * hP1 - hP2
  -- orderTop facts: genuineness of [n] and [−n], and the x-pole of [n]
  have hs_pos : 0 < s.orderTop := by
    rw [hs_def]
    refine orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W _ ?_
    rw [show (mulByInt W.toAffine n).pullback (x_gen W) = mulByInt_x W n from
      mulByInt_pullback_x W n hn]
    exact ordAtInfty_mulByInt_x_neg W n hn
  have hs'_pos : 0 < s'.orderTop := by
    rw [hs'_def]
    refine orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W _ ?_
    rw [show (mulByInt W.toAffine (-n)).pullback (x_gen W) = mulByInt_x W (-n) from
      mulByInt_pullback_x W (-n) hn', mulByInt_x_neg]
    exact ordAtInfty_mulByInt_x_neg W n hn
  have hA_ord : A.orderTop < 0 := by
    rw [hA_def, orderTop_localExpand_eq_ordAtInfty]
    exact ordAtInfty_mulByInt_x_neg W n hn
  -- extract integer orders; conclude B has a pole, so B⁻¹ has orderTop ≥ 1
  have hB_nt : B.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.2 hB_ne
  have hs_nt : s.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.2 hs_ne
  have hA_nt : A.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.2 hA_ne
  have h_ord_sum : B.orderTop + s.orderTop = A.orderTop := by
    have h := congrArg HahnSeries.orderTop hP1
    rwa [HahnSeries.orderTop_mul, HahnSeries.orderTop_neg] at h
  have hBinv_ord : (1 : WithTop ℤ) ≤ B⁻¹.orderTop := by
    rw [HahnSeries.orderTop_inv_eq_neg hB_ne]
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hB_nt
    obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hs_nt
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hA_nt
    rw [← hb, ← hσ, ← ha] at h_ord_sum
    have h1 : b + σ = a := by exact_mod_cast h_ord_sum
    have h2 : 0 < σ := by rw [← hσ] at hs_pos; exact_mod_cast hs_pos
    have h3 : a < 0 := by rw [← ha] at hA_ord; exact_mod_cast hA_ord
    rw [← hb, show -((b : WithTop ℤ)) = ((-b : ℤ) : WithTop ℤ) from rfl]
    exact_mod_cast (by omega : (1 : ℤ) ≤ -b)
  -- the bracket has orderTop ≥ 1
  have hbr_ord : (1 : WithTop ℤ) ≤
      (HahnSeries.single (0 : ℤ) W.a₁ * s - HahnSeries.single (0 : ℤ) W.a₃ * B⁻¹).orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    have hj1 : j < 1 := by exact_mod_cast hj
    rw [HahnSeries.coeff_sub, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul,
      HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul,
      HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_le_of_lt
        (show ((j : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) from by
          exact_mod_cast (by omega : j ≤ 0)) hs_pos),
      HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
        (show ((j : ℤ) : WithTop ℤ) < (1 : WithTop ℤ) from by exact_mod_cast hj1) hBinv_ord),
      smul_zero, smul_zero, sub_zero]
  -- s' has orderTop ≥ 1
  have hs'_one : (1 : WithTop ℤ) ≤ s'.orderTop := by
    rcases eq_or_ne s' 0 with h | h
    · rw [h, HahnSeries.orderTop_zero]; exact le_top
    · obtain ⟨σ', hσ'⟩ := WithTop.ne_top_iff_exists.mp (HahnSeries.orderTop_ne_top.2 h)
      rw [← hσ'] at hs'_pos ⊢
      exact_mod_cast (by exact_mod_cast hs'_pos : (0 : ℤ) < σ')
  -- the right side has coefficient 0 at index 1 (orderTop ≥ 2)
  have h_rhs_coeff : (s' * (HahnSeries.single (0 : ℤ) W.a₁ * s -
      HahnSeries.single (0 : ℤ) W.a₃ * B⁻¹)).coeff 1 = 0 := by
    refine HahnSeries.coeff_eq_zero_of_lt_orderTop ?_
    rw [HahnSeries.orderTop_mul]
    calc ((1 : ℤ) : WithTop ℤ) < ((2 : ℤ) : WithTop ℤ) := by exact_mod_cast one_lt_two
    _ = (1 : WithTop ℤ) + (1 : WithTop ℤ) := by rfl
    _ ≤ _ := add_le_add hs'_one hbr_ord
  -- conclude: coeff 1 of `s' + s` is 0
  have h_coeffs := congrArg (fun z : LaurentSeries F ↦ z.coeff 1) hL
  simp only [HahnSeries.coeff_add, h_rhs_coeff] at h_coeffs
  rw [formalIsogenySeries_coeff, formalIsogenySeries_coeff, Nat.cast_one, ← hs_def, ← hs'_def]
  exact eq_neg_of_add_eq_zero_left h_coeffs

/-- **L-F1 sub-leaf, restated (IV.2.3a, `m < 0`)**: `coeff 1 [m]_F = m` for negative `m`.
The negation step (`coeff_one_formalIsogenySeries_mulByInt_neg_eq`, axiom-clean) reduces to
the positive case, which is the BRIDGE-003 induction closer fed by the proven
`formalIsogenySeries_FGL_additivity`. Axiom-clean.

(B2 2026-06-11: the former `m ≤ 0` statement was false at `m = 0` —
see `coeff_one_formalIsogenySeries_mulByInt_zero`.) -/
theorem coeff_one_formalIsogenySeries_mulByInt_of_neg (m : ℤ) (hm : m < 0) :
    PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine m)) = (m : F) := by
  have h := coeff_one_formalIsogenySeries_mulByInt_neg_eq W (-m) (by omega)
  rw [neg_neg] at h
  rw [h]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((k : ℤ)) = -m := ⟨(-m).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  rw [← hk, coeff_one_formalIsogenySeries_mulByInt_via_bridge_003 W
    (formalIsogenySeries_FGL_additivity W) k hk1]
  have hm_eq : m = -((k : ℕ) : ℤ) := by omega
  rw [hm_eq]
  push_cast
  ring

/-- **L-F1** (Silverman IV.2.3a): `coeff 1 [m]_F = m` for `m ≠ 0`. (The `m = 0` instance is
false for the project's junk-`[0]`: see `coeff_one_formalIsogenySeries_mulByInt_zero`.) -/
theorem coeff_one_formalIsogenySeries_mulByInt_eq (m : ℤ) (hm : m ≠ 0) :
    PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine m)) = (m : F) := by
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · exact coeff_one_formalIsogenySeries_mulByInt_of_neg W m hneg
  · lift m to ℕ using hpos.le with n
    have hn : 1 ≤ n := by exact_mod_cast hpos
    exact_mod_cast coeff_one_formalIsogenySeries_mulByInt_via_bridge_003 W
      (formalIsogenySeries_FGL_additivity W) n hn

/-- **Product rule for the LaurentSeries formal derivative** (`= hasseDeriv 1`). Missing from
mathlib (`hasseDeriv 1` is only stated as a linear map); proved here via `coeff`. -/
theorem laurentSeries_derivative_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) :
    LaurentSeries.derivative R (f * g) =
      f * LaurentSeries.derivative R g + g * LaurentSeries.derivative R f := by
  ext m
  rw [show g * LaurentSeries.derivative R f = LaurentSeries.derivative R f * g from mul_comm _ _,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right,
    HahnSeries.coeff_add, LaurentSeries.derivative_apply, LaurentSeries.derivative_apply,
    HahnSeries.coeff_mul, HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  -- LHS: (m+1) • ∑_{AD_{f,g}(m+1)} f_i g_j.
  -- RHS sum₁ (f * Dg): reindex j ↦ j+1 onto AD_{f,g}(m+1), weight = j.
  have h1 : ∑ ij ∈ Finset.antidiagonal f.isPWO_support
        (LaurentSeries.hasseDeriv R 1 g).isPWO_support m,
        f.coeff ij.1 * (LaurentSeries.hasseDeriv R 1 g).coeff ij.2 =
      ∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (m + 1),
        ij.2 • (f.coeff ij.1 * g.coeff ij.2) := by
    have hcoeff : ∀ p : ℤ × ℤ,
        f.coeff p.1 * (LaurentSeries.hasseDeriv R 1 g).coeff p.2 =
          (p.2 + 1) • (f.coeff p.1 * g.coeff (p.2 + 1)) := by
      intro p
      rw [LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one, mul_smul_comm]
    have h_inj : Set.InjOn (fun p : ℤ × ℤ ↦ (p.1, p.2 + 1))
        ↑(Finset.antidiagonal f.isPWO_support
          (LaurentSeries.hasseDeriv R 1 g).isPWO_support m) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq, add_left_inj] at h
      exact Prod.ext h.1 h.2
    rw [Finset.sum_congr rfl (fun p _ ↦ hcoeff p),
      ← Finset.sum_image (f := fun q : ℤ × ℤ ↦ q.2 • (f.coeff q.1 * g.coeff q.2)) h_inj]
    refine Finset.sum_subset ?_ ?_
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [Finset.mem_antidiagonal] at hp ⊢
      refine ⟨hp.1, ?_, by rw [← hp.2.2]; ring⟩
      have : (LaurentSeries.hasseDeriv R 1 g).coeff p.2 ≠ 0 := hp.2.1
      rw [LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one] at this
      simp only [HahnSeries.mem_support, ne_eq]
      intro hg
      exact this (by rw [hg, smul_zero])
    · intro q hq hqnot
      rw [Finset.mem_antidiagonal] at hq
      rw [← mul_smul_comm]
      have : (q.2 : ℤ) • g.coeff q.2 = 0 := by
        by_contra hne
        apply hqnot
        rw [Finset.mem_image]
        refine ⟨(q.1, q.2 - 1), ?_, by simp⟩
        rw [Finset.mem_antidiagonal]
        refine ⟨hq.1, ?_, by have h := hq.2.2; show q.1 + (q.2 - 1) = m; omega⟩
        simp only [HahnSeries.mem_support, ne_eq]
        rw [LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one]
        intro hz
        apply hne
        have : (q.2 - 1 + 1 : ℤ) = q.2 := by ring
        rw [this] at hz
        exact hz
      rw [this, mul_zero]
  -- RHS sum₂ (Df * g): reindex i ↦ i+1 onto AD_{f,g}(m+1), weight = i.
  have h2 : ∑ ij ∈ Finset.antidiagonal (LaurentSeries.hasseDeriv R 1 f).isPWO_support
        g.isPWO_support m,
        (LaurentSeries.hasseDeriv R 1 f).coeff ij.1 * g.coeff ij.2 =
      ∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (m + 1),
        ij.1 • (f.coeff ij.1 * g.coeff ij.2) := by
    have hcoeff : ∀ p : ℤ × ℤ,
        (LaurentSeries.hasseDeriv R 1 f).coeff p.1 * g.coeff p.2 =
          (p.1 + 1) • (f.coeff (p.1 + 1) * g.coeff p.2) := by
      intro p
      rw [LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one, smul_mul_assoc]
    have h_inj : Set.InjOn (fun p : ℤ × ℤ ↦ (p.1 + 1, p.2))
        ↑(Finset.antidiagonal (LaurentSeries.hasseDeriv R 1 f).isPWO_support
          g.isPWO_support m) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq, add_left_inj] at h
      exact Prod.ext h.1 h.2
    rw [Finset.sum_congr rfl (fun p _ ↦ hcoeff p),
      ← Finset.sum_image (f := fun q : ℤ × ℤ ↦ q.1 • (f.coeff q.1 * g.coeff q.2)) h_inj]
    refine Finset.sum_subset ?_ ?_
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [Finset.mem_antidiagonal] at hp ⊢
      refine ⟨?_, hp.2.1, by rw [← hp.2.2]; ring⟩
      have : (LaurentSeries.hasseDeriv R 1 f).coeff p.1 ≠ 0 := hp.1
      rw [LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one] at this
      simp only [HahnSeries.mem_support, ne_eq]
      intro hf
      exact this (by rw [hf, smul_zero])
    · intro q hq hqnot
      rw [Finset.mem_antidiagonal] at hq
      rw [← smul_mul_assoc]
      have : (q.1 : ℤ) • f.coeff q.1 = 0 := by
        by_contra hne
        apply hqnot
        rw [Finset.mem_image]
        refine ⟨(q.1 - 1, q.2), ?_, by simp⟩
        rw [Finset.mem_antidiagonal]
        refine ⟨?_, hq.2.1, by have h := hq.2.2; show (q.1 - 1) + q.2 = m; omega⟩
        simp only [HahnSeries.mem_support, ne_eq]
        rw [LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one]
        intro hz
        apply hne
        have : (q.1 - 1 + 1 : ℤ) = q.1 := by ring
        rw [this] at hz
        exact hz
      rw [this, zero_mul]
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun ij hij ↦ ?_)
  rw [Finset.mem_antidiagonal] at hij
  rw [← add_smul, add_comm ij.2 ij.1, hij.2.2, Nat.cast_one]

omit [WeierstrassCurve.IsElliptic W.toAffine] in
/-- **L-KL.1** (Silverman IV.1): the formal derivative on `LaurentSeries F`, composed with the
ring hom `localExpand`, satisfies Leibniz — i.e. `f ↦ (d/dz)(localExpand f)` is a derivation.
Mathlib `LaurentSeries.derivative` (`= hasseDeriv 1`) + `localExpand` ring hom. -/
theorem localExpand_derivative_leibniz (f g : KE) :
    LaurentSeries.derivative F (localExpand W (f * g)) =
      localExpand W f * LaurentSeries.derivative F (localExpand W g) +
      localExpand W g * LaurentSeries.derivative F (localExpand W f) := by
  rw [map_mul]
  exact laurentSeries_derivative_mul (localExpand W f) (localExpand W g)

omit [WeierstrassCurve.IsElliptic W.toAffine] in
/-- `localExpand : KE →+* LaurentSeries F` is injective (it is `IsFractionRing.lift` of an
injective ring hom out of the coordinate ring). -/
theorem localExpand_injective : Function.Injective (localExpand W) :=
  (localExpand W).injective

omit [WeierstrassCurve.IsElliptic W.toAffine] in
/-- The formal `t`-derivative of the local expansion of a constant `algebraMap F KE r` is `0`
(the local expansion is a constant Laurent series). Used for the `F`-linearity of the
`localExpand`-derivation. -/
theorem derivative_localExpand_algebraMap (r : F) :
    LaurentSeries.derivative F (localExpand W (algebraMap F KE r)) = 0 := by
  rw [localExpand_algebraMap, HahnSeries.ofPowerSeries_C, LaurentSeries.derivative_apply,
    show (HahnSeries.C r : LaurentSeries F) = HahnSeries.single (0 : ℤ) r from rfl,
    LaurentSeries.hasseDeriv_single]
  simp

/-! ### The `localExpand`-Kähler lift `Ω[K(E)/F] → LaurentSeries F` (Silverman IV.4.3 setup)

The derivation `g ↦ (d/dt)(localExpand g)` on `K(E)`, valued in `LaurentSeries F` regarded as a
`K(E)`-module via `localExpand`, lifts through the universal property to an additive map
`Ω[K(E)/F] → LaurentSeries F` sending `D g ↦ (d/dt)(localExpand g)` and respecting the `K(E)`-scalar
action (`c • ω ↦ localExpand c · (image of ω)`). This is the "missing setup" for IV.4.3: applying
the lift to `omegaPullbackCoeff_spec` turns the Kähler identity `a_α • ω = (α*u)⁻¹ • D(α*x)` into a
Laurent-series identity whose coefficients can be read off.

Mirrors the `TwistedKaehler` wrapper pattern of `Auxiliary/PullbackKaehler.lean`: a wrapper carries
the `K(E)`-module structure (via `localExpand`) and an `F`-module restricted through `algebraMap F
K(E)`,
so the `IsScalarTower F K(E) _` needed by `liftKaehlerDifferential` holds by construction
(sidestepping
the `SMul F (LaurentSeries F)` instance diamond). -/

/-- Wrapper for `LaurentSeries F` carrying the `K(E)`-module structure via `localExpand`. -/
structure LExp (W : WeierstrassCurve F) [W.toAffine.IsElliptic] where
  mk' ::
  /-- The underlying Laurent series. -/
  out : LaurentSeries F

namespace LExp
variable {W}

omit [DecidableEq F] in
@[ext] theorem ext {x y : LExp W} (h : x.out = y.out) : x = y := by cases x; cases y; congr

noncomputable instance : Zero (LExp W) := ⟨⟨0⟩⟩
noncomputable instance : Add (LExp W) := ⟨fun x y ↦ ⟨x.out + y.out⟩⟩
noncomputable instance : Neg (LExp W) := ⟨fun x ↦ ⟨-x.out⟩⟩
noncomputable instance : Sub (LExp W) := ⟨fun x y ↦ ⟨x.out - y.out⟩⟩
omit [DecidableEq F] in
@[simp] theorem out_zero : (0 : LExp W).out = 0 := rfl
omit [DecidableEq F] in
@[simp] theorem out_add (x y : LExp W) : (x + y).out = x.out + y.out := rfl
omit [DecidableEq F] in
@[simp] theorem out_neg (x : LExp W) : (-x).out = -x.out := rfl
omit [DecidableEq F] in
@[simp] theorem out_sub (x y : LExp W) : (x - y).out = x.out - y.out := rfl

noncomputable instance : AddCommGroup (LExp W) where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  add_comm x y := by ext; simp [add_comm]
  neg_add_cancel x := by ext; simp
  sub_eq_add_neg x y := by ext; simp [sub_eq_add_neg]
  zsmul := zsmulRec
  nsmul := nsmulRec

/-- `K(E)` acts on the wrapper via `localExpand`-multiplication. -/
noncomputable instance instSMulKE : SMul KE (LExp W) where
  smul c x := ⟨localExpand W c * x.out⟩
@[simp] theorem out_smul_KE (c : KE) (x : LExp W) : (c • x).out = localExpand W c * x.out := rfl

noncomputable instance instModuleKE : Module KE (LExp W) where
  one_smul x := by ext; simp [out_smul_KE]
  mul_smul c d x := by ext; simp [out_smul_KE, map_mul, mul_assoc]
  smul_zero c := by ext; simp [out_smul_KE]
  smul_add c x y := by ext; simp [out_smul_KE, mul_add]
  add_smul c d x := by ext; simp [out_smul_KE, map_add, add_mul]
  zero_smul x := by ext; simp [out_smul_KE]

/-- `F` acts on the wrapper by restriction through `algebraMap F K(E)`, making the scalar tower
`F → K(E) → LExp` hold by construction. -/
noncomputable instance instSMulF : SMul F (LExp W) where
  smul r x := (algebraMap F KE r) • x
@[simp] theorem out_smul_F (r : F) (x : LExp W) :
    (r • x : LExp W).out = localExpand W (algebraMap F KE r) * x.out := rfl

noncomputable instance instModuleF : Module F (LExp W) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [map_mul, mul_assoc]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [mul_add]
  add_smul r s x := by ext; simp [map_add, add_mul]
  zero_smul x := by ext; simp

instance : IsScalarTower F KE (LExp W) := by
  refine ⟨fun r c x ↦ ?_⟩
  ext
  simp only [out_smul_KE, out_smul_F]
  rw [show (r • c : KE) = algebraMap F KE r * c from Algebra.smul_def r c, map_mul, mul_assoc]

end LExp

/-- The derivation `g ↦ (d/dt)(localExpand g)` from `K(E)` to `LaurentSeries F` (regarded as a
`K(E)`-module via `localExpand`). Leibniz is `localExpand_derivative_leibniz`; `F`-linearity is the
constant-pullout `derivative_localExpand_algebraMap`. -/
noncomputable def localExpandDeriv : Derivation F KE (LExp W) where
  toFun g := ⟨LaurentSeries.derivative F (localExpand W g)⟩
  map_add' x y := by ext; simp [map_add]
  map_smul' r x := by
    refine LExp.ext ?_
    simp only [RingHom.id_apply, LExp.out_smul_F]
    show LaurentSeries.derivative F (localExpand W (r • x)) =
      localExpand W (algebraMap F KE r) * LaurentSeries.derivative F (localExpand W x)
    rw [show (r • x : KE) = algebraMap F KE r * x from Algebra.smul_def r x, map_mul,
      laurentSeries_derivative_mul, derivative_localExpand_algebraMap, mul_zero, add_zero]
  map_one_eq_zero' := by
    refine LExp.ext ?_
    show LaurentSeries.derivative F (localExpand W 1) = 0
    rw [map_one, LaurentSeries.derivative_apply,
      show (1 : LaurentSeries F) = HahnSeries.single (0 : ℤ) 1 from
        HahnSeries.single_zero_one.symm,
      LaurentSeries.hasseDeriv_single]
    simp
  leibniz' x y := by
    refine LExp.ext ?_
    show LaurentSeries.derivative F (localExpand W (x * y)) =
      (x • (⟨LaurentSeries.derivative F (localExpand W y)⟩ : LExp W) +
       y • (⟨LaurentSeries.derivative F (localExpand W x)⟩ : LExp W)).out
    rw [localExpand_derivative_leibniz]
    simp only [LExp.out_add, LExp.out_smul_KE]

/-- The lift of `localExpandDeriv` through the universal property of Kähler differentials:
`Ω[K(E)/F] →ₗ[K(E)] LExp W`, characterised by `D g ↦ (d/dt)(localExpand g)`. -/
noncomputable def localExpandKaehlerLift : KaehlerDifferential F KE →ₗ[KE] LExp W :=
  (localExpandDeriv W).liftKaehlerDifferential

/-- The lift sends `D g` to the formal `t`-derivative of `localExpand g`. -/
theorem localExpandKaehlerLift_D (g : KE) :
    (localExpandKaehlerLift W (KaehlerDifferential.D F KE g)).out =
      LaurentSeries.derivative F (localExpand W g) := by
  rw [localExpandKaehlerLift, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- The lift is `K(E)`-semilinear: a `K(E)`-scalar `c` becomes `localExpand c`. -/
theorem localExpandKaehlerLift_smul (c : KE) (ω : KaehlerDifferential F KE) :
    (localExpandKaehlerLift W (c • ω)).out =
      localExpand W c * (localExpandKaehlerLift W ω).out := by
  simp only [map_smul, LExp.out_smul_KE]

/-! ### Direct Frobenius instances

The Frobenius coefficient is zero, so its integrality, nonnegative infinity order,
and membership in the base field follow directly. These proofs remain independent
of the general regularity and integrality arguments below. The finite-field
hypothesis is required by `frobeniusIsog`. -/

/-- **Wave 2.0 PASS leaf (Leaf 1.π)** — `a_π` is integral over `F[X]`.
Trivial since `a_π = 0 = algebraMap _ _ 0` ∈ algebraMap image. Axiom-clean. -/
theorem omegaPullbackCoeff_isIntegral_polynomialX_frobenius
    [Fintype F] :
    IsIntegral (Polynomial F) (omegaPullbackCoeff W (frobeniusIsog W)) := by
  rw [omegaPullbackCoeff_frobenius]
  exact isIntegral_zero

/-- **Wave 2.0 PASS leaf (Leaf 2.π)** — `a_π` has nonneg ord at infinity.
Trivial since `a_π = 0` and `ord_∞ 0 = ⊤ ≥ 0`. Axiom-clean. -/
theorem omegaPullbackCoeff_ordAtInfty_nonneg_frobenius
    [Fintype F] :
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty
        (omegaPullbackCoeff W (frobeniusIsog W)) := by
  rw [omegaPullbackCoeff_frobenius, HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero]
  exact le_top

/-- **Wave 2.0 PASS leaf (Leaf 3.π) — `mem_F` for α = π specifically**
(Silverman III.1.5 corollary for Frobenius). Axiom-clean discharge composing
the two per-α PASS sub-leaves with the shipped algebraic-Liouville theorem. -/
theorem omegaPullbackCoeff_mem_F_frobenius
    [Fintype F] :
    ∃ c : F, omegaPullbackCoeff W (frobeniusIsog W) = algebraMap F KE c := by
  have h_int := omegaPullbackCoeff_isIntegral_polynomialX_frobenius W
  have h_inf := omegaPullbackCoeff_ordAtInfty_nonneg_frobenius W
  exact HasseWeil.Curves.SmoothPlaneCurve.const_of_isIntegral_polynomialX_of_ordAtInfty
    (C := (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F)) h_int h_inf

/-! ### Witness-parametric COMPOSITION closure for mem_F

Given mem_F witnesses for both `α` and `β`, derives mem_F for `α.comp β`
via the chain rule `omegaPullbackCoeff_comp_of_base`. Axiom-clean. -/

/-- **Wave 2.0 PASS closure — `mem_F` for compositions**. Given mem_F for `α`
and `β` (as explicit `c_α, c_β ∈ F` witnesses), produces mem_F for `α.comp β`
via the chain rule. The combined constant is `c_α · c_β`. Axiom-clean. -/
theorem omegaPullbackCoeff_mem_F_comp_of_witnesses
    (α β : Isogeny W.toAffine W.toAffine)
    (c_α c_β : F)
    (hα : omegaPullbackCoeff W α = algebraMap F KE c_α)
    (hβ : omegaPullbackCoeff W β = algebraMap F KE c_β) :
    ∃ c : F, omegaPullbackCoeff W (α.comp β) = algebraMap F KE c := by
  refine ⟨c_α * c_β, ?_⟩
  rw [omegaPullbackCoeff_comp_of_base W α β c_α hα, hβ, ← map_mul]

/-- **Wave 2.0 PASS closure — `mem_F` from existential witnesses**. The
purely-existential form (no explicit `c_α, c_β`). Useful as a composition
closer when only the existential mem_F facts are available. Axiom-clean. -/
theorem omegaPullbackCoeff_mem_F_comp_of_mem_F
    (α β : Isogeny W.toAffine W.toAffine)
    (hα : ∃ c : F, omegaPullbackCoeff W α = algebraMap F KE c)
    (hβ : ∃ c : F, omegaPullbackCoeff W β = algebraMap F KE c) :
    ∃ c : F, omegaPullbackCoeff W (α.comp β) = algebraMap F KE c := by
  obtain ⟨c_α, hα⟩ := hα
  obtain ⟨c_β, hβ⟩ := hβ
  exact omegaPullbackCoeff_mem_F_comp_of_witnesses W α β c_α c_β hα hβ

/-- **Wave 2.0 PASS closure — `mem_F` propagation through additivity**. Given
mem_F for `α` and `β`, AND the additivity hypothesis `omega(γ) = omega(α) + omega(β)`
(supplied as a witness — its discharge is via the BRIDGE / RB-ADD chain
shipped axiom-clean elsewhere), derives mem_F for `γ`. Axiom-clean. -/
theorem omegaPullbackCoeff_mem_F_of_add_witness
    (α β γ : Isogeny W.toAffine W.toAffine)
    (hα : ∃ c : F, omegaPullbackCoeff W α = algebraMap F KE c)
    (hβ : ∃ c : F, omegaPullbackCoeff W β = algebraMap F KE c)
    (h_add : omegaPullbackCoeff W γ =
      omegaPullbackCoeff W α + omegaPullbackCoeff W β) :
    ∃ c : F, omegaPullbackCoeff W γ = algebraMap F KE c := by
  obtain ⟨c_α, hα⟩ := hα
  obtain ⟨c_β, hβ⟩ := hβ
  refine ⟨c_α + c_β, ?_⟩
  rw [h_add, hα, hβ, ← map_add]

/-! ### Witness-parametric CHORD-STEP closure for mem_F: `addIsog (id, α)`

Given mem_F for `α`, derive mem_F for `addIsog (id, α)` (= `1 + α`) via the
shipped chord step `omegaPullbackCoeff_addIsog_id` (axiom-clean,
`HasseWeil/RouteBInduction.lean:35`). The combined constant is `1 + c_α`.
Axiom-clean. -/

/-- **Wave 2.0 PASS closure — `mem_F` for `addIsog (id, α)`**. Given mem_F for
`α` plus the standard AddNonInversePair + injectivity + x-mismatch witnesses
for the `(id, α)` pair, derive mem_F for the sum isogeny `(id ⊞ α)`. The
combined constant is `1 + c_α`. Axiom-clean via `omegaPullbackCoeff_addIsog_id`. -/
theorem omegaPullbackCoeff_mem_F_addIsog_id_of_witness
    [Fintype F]
    (α : Isogeny W.toAffine W.toAffine)
    (hxy : AddNonInversePair (Isogeny.id W.toAffine) α)
    (hinj : Function.Injective (addCoordAlgHomPair hxy))
    (h_ne : x_gen W ≠ α.pullback (x_gen W))
    (c_α : F)
    (hα : omegaPullbackCoeff W α = algebraMap F KE c_α) :
    ∃ c : F, omegaPullbackCoeff W (addIsog hxy hinj) = algebraMap F KE c := by
  refine ⟨1 + c_α, ?_⟩
  rw [omegaPullbackCoeff_addIsog_id W α hxy hinj h_ne, hα, map_add, map_one]

/-! ### Universal mem_F closures via inseparable-leading isogeny composition

If `omega(α) = 0` (purely inseparable α — e.g., Frobenius, negFrobenius), then
the chain rule `omega(α.comp β) = omega(α) · omega(β) = 0 · omega(β) = 0`
gives `omega(α.comp β) = 0` for ANY β. This is universal in β. Axiom-clean
via `omegaPullbackCoeff_comp_of_base` instantiated at `c_α = 0`. -/

/-- **Wave 2.0 PASS closure — UNIVERSAL `mem_F` for compositions with omega-zero leading α**.
Given a witness `omega(α) = 0` (purely inseparable α), derives mem_F for `α.comp β`
for ANY β (the omega is identically 0, so c = 0 ∈ F).

Particularly useful for α ∈ {`frobeniusIsog`, `negFrobeniusIsog`}: their compositions
with any isogeny β have mem_F trivially. -/
theorem omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading
    (α β : Isogeny W.toAffine W.toAffine)
    (hα : omegaPullbackCoeff W α = 0) :
    ∃ c : F, omegaPullbackCoeff W (α.comp β) = algebraMap F KE c := by
  refine ⟨0, ?_⟩
  rw [omegaPullbackCoeff_comp_of_base W α β 0 (by rw [hα, map_zero]), map_zero, zero_mul]

/-- **Wave 2.0 PASS leaf — UNIVERSAL `mem_F` for `frobeniusIsog.comp β`**.
Direct application of `omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading`
to α = Frobenius. Axiom-clean. -/
theorem omegaPullbackCoeff_mem_F_frobeniusIsog_comp
    [Fintype F]
    (β : Isogeny W.toAffine W.toAffine) :
    ∃ c : F, omegaPullbackCoeff W ((frobeniusIsog W).comp β) =
      algebraMap F KE c :=
  omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading W (frobeniusIsog W) β
    (omegaPullbackCoeff_frobenius W)

/-- **Wave 2.0 PASS leaf — UNIVERSAL `mem_F` for `negFrobeniusIsog.comp β`**.
Direct application of `omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading`
to α = negFrobenius. Axiom-clean. -/
theorem omegaPullbackCoeff_mem_F_negFrobeniusIsog_comp
    [Fintype F]
    (β : Isogeny W.toAffine W.toAffine) :
    ∃ c : F, omegaPullbackCoeff W ((negFrobeniusIsog W).comp β) =
      algebraMap F KE c :=
  omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading W (negFrobeniusIsog W) β
    (omegaPullbackCoeff_negFrobeniusIsog W)

/-! ### Per-α PASS leaves for α = `Isogeny.id W.toAffine` (the identity)

Trivial via the shipped closed form `omegaPullbackCoeff_id = 1`
(`HasseWeil/FormalIsogenySeries.lean:652`, axiom-clean). The identity baseline
for the entire per-α dispatch chain. -/

/-- **Wave 2.0 PASS leaf (Leaf 1.id)** — `a_id` is integral over `F[X]`.
Trivial: `a_id = 1` is integral. Axiom-clean. -/
theorem omegaPullbackCoeff_isIntegral_polynomialX_id :
    IsIntegral (Polynomial F) (omegaPullbackCoeff W (Isogeny.id W.toAffine)) := by
  rw [omegaPullbackCoeff_id]
  exact isIntegral_one

/-- **Wave 2.0 PASS leaf (Leaf 2.id)** — `a_id` has nonneg ord at infinity.
Trivial: `a_id = 1` and `ord_∞ 1 = 0 ≥ 0`. Axiom-clean. -/
theorem omegaPullbackCoeff_ordAtInfty_nonneg_id :
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty
        (omegaPullbackCoeff W (Isogeny.id W.toAffine)) := by
  rw [omegaPullbackCoeff_id]
  show (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (1 : KE)
  have h_one : (1 : KE) = algebraMap F KE 1 := (map_one _).symm
  rw [h_one, ordAtInfty_algebraMap_F_nonzero (W := W) (one_ne_zero)]

/-- **Wave 2.0 PASS leaf (Leaf 3.id) — `mem_F` for α = identity**
(Silverman III.1.5 corollary, identity baseline). Axiom-clean. -/
theorem omegaPullbackCoeff_mem_F_id :
    ∃ c : F, omegaPullbackCoeff W (Isogeny.id W.toAffine) = algebraMap F KE c :=
  ⟨1, by rw [omegaPullbackCoeff_id, map_one]⟩

/-! ### Per-α PASS leaves for α = `mulByInt n` (n ≠ 0)

Trivial via the AXIOM-CLEAN closed-form `omegaPullbackCoeff_mulByInt_routeB W n hn =
algebraMap F KE n` (`HasseWeil/RouteBInduction.lean:179`, Wronskian-free).
Provides the W4-A.1 chain's `mulByInt` half without needing the III.1 substrate
development. `[Fintype F]` inherited from routeB. -/

/-- **Wave 2.0 PASS leaf (Leaf 1.[n])** — `a_[n]` is integral over `F[X]`.
Trivial: `a_[n] = algebraMap F KE n` which is in the algebraMap image, hence
integral. Axiom-clean (via routeB). -/
theorem omegaPullbackCoeff_isIntegral_polynomialX_mulByInt
    [Fintype F]
    (n : ℤ) (hn : n ≠ 0) :
    IsIntegral (Polynomial F) (omegaPullbackCoeff W (mulByInt W.toAffine n)) := by
  rw [omegaPullbackCoeff_mulByInt_routeB W n hn]
  exact isIntegral_algebraMap

/-- **Wave 2.0 PASS leaf (Leaf 2.[n])** — `a_[n]` has nonneg ord at infinity.
Trivial: `a_[n] = algebraMap F KE n`. If `(n:F) = 0` then `a_[n] = 0` and
`ord_∞ 0 = ⊤ ≥ 0`; if `(n:F) ≠ 0` then `ord_∞ = 0 ≥ 0`. Axiom-clean (via routeB). -/
theorem omegaPullbackCoeff_ordAtInfty_nonneg_mulByInt
    [Fintype F]
    (n : ℤ) (hn : n ≠ 0) :
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty
        (omegaPullbackCoeff W (mulByInt W.toAffine n)) := by
  rw [omegaPullbackCoeff_mulByInt_routeB W n hn]
  by_cases hnF : (n : F) = 0
  · rw [hnF, map_zero, HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero]
    exact le_top
  · show (0 : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty ((algebraMap F KE) ((n : F)))
    rw [ordAtInfty_algebraMap_F_nonzero (W := W) hnF]

/-- **Wave 2.0 PASS leaf (Leaf 3.[n]) — `mem_F` for α = `mulByInt n` specifically**
(Silverman III.1.5 corollary for `[n]`). Axiom-clean: direct from the routeB
closed form. -/
theorem omegaPullbackCoeff_mem_F_mulByInt
    [Fintype F]
    (n : ℤ) (hn : n ≠ 0) :
    ∃ c : F, omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE c :=
  ⟨(n : F), omegaPullbackCoeff_mulByInt_routeB W n hn⟩

/-! ### Per-α PASS leaves for α = `negFrobeniusIsog` (= `[−1] ∘ π`)

Axiom-clean via the shipped closed form `omegaPullbackCoeff_negFrobeniusIsog = 0`
(`AdditionPullback/Differential.lean:417`). Provides the negFrobeniusIsog half
of the W4-A.1 chain without III.1 substrate. `[Fintype F]` inherited from
`frobeniusIsog`. -/

/-- **Wave 2.0 PASS leaf (Leaf 1.−π)** — `a_(−π)` is integral over `F[X]`.
Trivial: `a_(−π) = 0` ∈ algebraMap image, hence integral. Axiom-clean. -/
theorem omegaPullbackCoeff_isIntegral_polynomialX_negFrobenius
    [Fintype F] :
    IsIntegral (Polynomial F) (omegaPullbackCoeff W (negFrobeniusIsog W)) := by
  rw [omegaPullbackCoeff_negFrobeniusIsog]
  exact isIntegral_zero

/-- **Wave 2.0 PASS leaf (Leaf 2.−π)** — `a_(−π)` has nonneg ord at infinity.
Trivial: `a_(−π) = 0` and `ord_∞ 0 = ⊤ ≥ 0`. Axiom-clean. -/
theorem omegaPullbackCoeff_ordAtInfty_nonneg_negFrobenius
    [Fintype F] :
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty
        (omegaPullbackCoeff W (negFrobeniusIsog W)) := by
  rw [omegaPullbackCoeff_negFrobeniusIsog, HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero]
  exact le_top

/-- **Wave 2.0 PASS leaf (Leaf 3.−π) — `mem_F` for α = `negFrobeniusIsog`
specifically** (Silverman III.1.5 corollary for `−π`). Axiom-clean: direct
from the closed-form `omega = 0`. -/
theorem omegaPullbackCoeff_mem_F_negFrobenius
    [Fintype F] :
    ∃ c : F, omegaPullbackCoeff W (negFrobeniusIsog W) = algebraMap F KE c :=
  ⟨0, by rw [omegaPullbackCoeff_negFrobeniusIsog, map_zero]⟩

/-! ### Per-α PASS leaves for α = `isogOneSub_negFrobenius` (= `1 + π`,
the key isogeny for the Hasse bound)

Axiom-clean via the shipped closed form `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`
(`AdditionPullback/SilvermanIV14.lean:3927`). This is the key isogeny: `omega = 1` ⟹
`a_(1+π) = 1` ⟹ `(1+π)` is **separable** (Silverman III.5.5, the converse direction
that makes Wave-2 actionable). `[Fact p.Prime] [CharP F p] [Fintype F]` inherited. -/

/-- **Wave 2.0 PASS leaf (Leaf 1.1+π)** — `a_(1+π)` is integral over `F[X]`.
Trivial: `a_(1+π) = 1` ∈ algebraMap image (as `algebraMap F KE 1 = 1`),
hence integral. Axiom-clean. -/
theorem omegaPullbackCoeff_isIntegral_polynomialX_isogOneSub_negFrobenius
    [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hq : 2 ≤ Fintype.card F) :
    IsIntegral (Polynomial F)
      (omegaPullbackCoeff W (isogOneSub_negFrobenius W hq)) := by
  rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq]
  exact isIntegral_one

/-- **Wave 2.0 PASS leaf (Leaf 2.1+π)** — `a_(1+π)` has nonneg ord at infinity.
Trivial: `a_(1+π) = 1` and `ord_∞ 1 = 0 ≥ 0`. Axiom-clean. -/
theorem omegaPullbackCoeff_ordAtInfty_nonneg_isogOneSub_negFrobenius
    [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hq : 2 ≤ Fintype.card F) :
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty
        (omegaPullbackCoeff W (isogOneSub_negFrobenius W hq)) := by
  rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq]
  show (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (1 : KE)
  have h_one : (1 : KE) = algebraMap F KE 1 := (map_one _).symm
  rw [h_one, ordAtInfty_algebraMap_F_nonzero (W := W) (one_ne_zero)]

/-- **Wave 2.0 PASS leaf (Leaf 3.1+π) — `mem_F` for the KEY isogeny `(1+π)`**
(Silverman III.1.5 corollary for the Hasse-bound isogeny). Axiom-clean: direct
from the closed-form `omega = 1`. -/
theorem omegaPullbackCoeff_mem_F_isogOneSub_negFrobenius
    [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hq : 2 ≤ Fintype.card F) :
    ∃ c : F, omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap F KE c :=
  ⟨1, by rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq, map_one]⟩

/-! ### IV.4.2 normalization toolkit: Laurent-coefficient bricks

Leading-coefficient extraction for the invariant-differential normalization (N) below.
The two abstract bricks (`laurent_orderTop_eq_of_coeff`,
`laurent_coeff_eq_leadingCoeff_of_orderTop`) convert explicit coefficient computations into
`orderTop`/`leadingCoeff` data, which then flows through the multiplicative
`orderTop_mul`/`leadingCoeff_mul`/`orderTop_inv_eq_neg`/`leadingCoeff_inv` calculus. -/

omit [DecidableEq F] in
/-- A Laurent series whose coefficients vanish below `d` and whose `d`-coefficient is
nonzero has `orderTop = d`. -/
theorem laurent_orderTop_eq_of_coeff {f : LaurentSeries F} {d : ℤ}
    (h0 : ∀ j : ℤ, j < d → f.coeff j = 0) (hd : f.coeff d ≠ 0) :
    f.orderTop = (d : WithTop ℤ) := by
  refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hd) ?_
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  exact h0 j (by exact_mod_cast hj)

omit [DecidableEq F] in
/-- If `orderTop f = d` then the `d`-th coefficient is the leading coefficient. -/
theorem laurent_coeff_eq_leadingCoeff_of_orderTop {f : LaurentSeries F} {d : ℤ}
    (h : f.orderTop = (d : WithTop ℤ)) : f.coeff d = f.leadingCoeff := by
  have hne : f ≠ 0 := by
    intro h0
    rw [h0, HahnSeries.orderTop_zero] at h
    exact WithTop.top_ne_coe h
  have hnt : f.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.2 hne
  have huntop : f.orderTop.untop hnt = d := by
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, h]
  rw [← HahnSeries.coeff_untop_eq_leadingCoeff hnt, huntop]

omit [DecidableEq F] in
/-- Coefficient formula for the formal derivative on `LaurentSeries`. -/
theorem laurent_derivative_coeff (f : LaurentSeries F) (m : ℤ) :
    (LaurentSeries.derivative F f).coeff m = (m + 1) • f.coeff (m + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right,
    Nat.cast_one]

omit [DecidableEq F] in
/-- The formal derivative kills constants `single 0 a`. -/
theorem laurent_derivative_single_zero (a : F) :
    LaurentSeries.derivative F (HahnSeries.single (0 : ℤ) a) = 0 := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single]
  simp

omit [DecidableEq F] in
/-- Coefficients of `ofPowerSeries` Laurent series vanish at negative indices. -/
theorem laurent_ofPowerSeries_coeff_neg (g : PowerSeries F) {j : ℤ} (hj : j < 0) :
    (HahnSeries.ofPowerSeries ℤ F g).coeff j = 0 := by
  have hnr : j ∉ Set.range ((↑) : ℕ → ℤ) := by rintro ⟨n, rfl⟩; omega
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range hnr

omit [DecidableEq F] in
/-- `ofPowerSeries` Laurent series have nonnegative `orderTop`. -/
theorem laurent_ofPowerSeries_orderTop_nonneg (g : PowerSeries F) :
    (0 : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ F g).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  exact laurent_ofPowerSeries_coeff_neg g (by exact_mod_cast hj)

omit [DecidableEq F] in
/-- `ofPowerSeries` of a power series with zero constant coefficient has `orderTop ≥ 1`. -/
theorem laurent_ofPowerSeries_orderTop_one_le (g : PowerSeries F)
    (hg : PowerSeries.constantCoeff g = 0) :
    (1 : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ F g).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  have hj1 : j < 1 := by exact_mod_cast hj
  rcases lt_or_eq_of_le (by omega : j ≤ 0) with h | h
  · exact laurent_ofPowerSeries_coeff_neg g h
  · subst h
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg

omit [DecidableEq F] in
/-- The Laurent formal derivative commutes with `ofPowerSeries`:
`(d/dt)(ofPS g) = ofPS (d⁄dX g)`. Coefficientwise check (negative indices vanish on
both sides; nonnegative indices are `PowerSeries.coeff_derivative`). -/
theorem laurent_derivative_ofPowerSeries (g : PowerSeries F) :
    LaurentSeries.derivative F (HahnSeries.ofPowerSeries ℤ F g) =
      HahnSeries.ofPowerSeries ℤ F (d⁄dX F g) := by
  ext m
  rw [laurent_derivative_coeff]
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) from by push_cast; ring,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_derivative, zsmul_eq_mul]
    push_cast
    ring
  · rcases lt_or_eq_of_le (by omega : m + 1 ≤ 0) with h | h
    · rw [laurent_ofPowerSeries_coeff_neg g h, smul_zero,
        laurent_ofPowerSeries_coeff_neg (d⁄dX F g) hm]
    · rw [h, zero_smul, laurent_ofPowerSeries_coeff_neg (d⁄dX F g) hm]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- Coefficients of `formalX` vanish below `-2`. -/
theorem formalX_coeff_of_lt {j : ℤ} (hj : j < -2) : (formalX W).coeff j = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_orderTop (by rw [formalX_orderTop]; exact_mod_cast hj)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- The leading coefficient of `formalX` at `t⁻²` is `1`. -/
theorem formalX_coeff_neg_two : (formalX W).coeff (-2) = 1 := by
  rw [laurent_coeff_eq_leadingCoeff_of_orderTop (formalX_orderTop W), formalX_leadingCoeff]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- Coefficients of `formalY` vanish below `-3`. -/
theorem formalY_coeff_of_lt {j : ℤ} (hj : j < -3) : (formalY W).coeff j = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_orderTop (by rw [formalY_orderTop]; exact_mod_cast hj)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- The leading coefficient of `formalY` at `t⁻³` is `-1`. -/
theorem formalY_coeff_neg_three : (formalY W).coeff (-3) = -1 := by
  rw [laurent_coeff_eq_leadingCoeff_of_orderTop (formalY_orderTop W), formalY_leadingCoeff]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- `formalX ^ 2` has `orderTop = -4`. -/
theorem formalX_sq_orderTop : ((formalX W) ^ 2).orderTop = ((-4 : ℤ) : WithTop ℤ) := by
  rw [sq, HahnSeries.orderTop_mul, formalX_orderTop]
  rfl

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- Coefficients of `formalX ^ 2` vanish below `-4`. -/
theorem formalX_sq_coeff_of_lt {j : ℤ} (hj : j < -4) : ((formalX W) ^ 2).coeff j = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_orderTop (by rw [formalX_sq_orderTop]; exact_mod_cast hj)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- The leading coefficient of `formalX ^ 2` at `t⁻⁴` is `1`. -/
theorem formalX_sq_coeff_neg_four : ((formalX W) ^ 2).coeff (-4) = 1 := by
  rw [laurent_coeff_eq_leadingCoeff_of_orderTop (formalX_sq_orderTop W), sq,
    HahnSeries.leadingCoeff_mul, formalX_leadingCoeff, mul_one]

omit [WeierstrassCurve.IsElliptic W.toAffine] in
/-- `localExpand u_gen` as an explicit Laurent-series sum (numeral-free: `2y` is `y + y`). -/
theorem localExpand_u_gen :
    localExpand W (u_gen W) =
      formalY W + formalY W + HahnSeries.single (0 : ℤ) W.a₁ * formalX W +
        HahnSeries.single (0 : ℤ) W.a₃ := by
  have hx : algebraMap W.toAffine.CoordinateRing KE
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) = x_gen W := rfl
  have hy : algebraMap W.toAffine.CoordinateRing KE
      (AdjoinRoot.root W.toAffine.polynomial) = y_gen W := rfl
  rw [u_gen, hx, hy, map_add, map_add, map_mul, map_mul, map_ofNat, localExpand_x_gen,
    localExpand_y_gen, localExpand_algebraMap, localExpand_algebraMap,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C,
    show (HahnSeries.C W.a₁ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₁ from rfl,
    show (HahnSeries.C W.a₃ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₃ from rfl]
  ring

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- The `t`-derivative of the Weierstrass relation between `formalX` and `formalY`:
`(2y + a₁x + a₃)·y′ = (3x² + 2a₂x + a₄ − a₁y)·x′` in `LaurentSeries F`, spelled with
numeral-free sums. Differentiates `formalXY_weierstrass` term-by-term with the product rule
`laurentSeries_derivative_mul` and rearranges. This is the implicit-differentiation identity
behind the two denominators `u = 2y + a₁x + a₃` and `v = 3x² + 2a₂x + a₄ − a₁y` of the
invariant differential (Silverman III.1 (3.1.4)/IV.4.2). -/
theorem formalXY_weierstrass_derivative :
    (formalY W + formalY W + HahnSeries.single (0 : ℤ) W.a₁ * formalX W +
        HahnSeries.single (0 : ℤ) W.a₃) * LaurentSeries.derivative F (formalY W) =
      (formalX W ^ 2 + formalX W ^ 2 + formalX W ^ 2 +
        (HahnSeries.single (0 : ℤ) W.a₂ * formalX W +
          HahnSeries.single (0 : ℤ) W.a₂ * formalX W) +
        HahnSeries.single (0 : ℤ) W.a₄ -
        HahnSeries.single (0 : ℤ) W.a₁ * formalY W) * LaurentSeries.derivative F (formalX W) := by
  have hW := formalXY_weierstrass W
  simp only [HahnSeries.ofPowerSeries_C,
    show (HahnSeries.C W.a₁ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₁ from rfl,
    show (HahnSeries.C W.a₂ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₂ from rfl,
    show (HahnSeries.C W.a₃ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₃ from rfl,
    show (HahnSeries.C W.a₄ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₄ from rfl,
    show (HahnSeries.C W.a₆ : LaurentSeries F) = HahnSeries.single (0 : ℤ) W.a₆ from rfl] at hW
  have hD := congrArg (⇑(LaurentSeries.derivative F)) hW
  simp only [map_sub, map_add, map_zero] at hD
  -- expand the seven derivative terms via the product rule
  have hsq : LaurentSeries.derivative F (formalX W ^ 2) =
      formalX W * LaurentSeries.derivative F (formalX W) +
        formalX W * LaurentSeries.derivative F (formalX W) := by
    rw [sq]; exact laurentSeries_derivative_mul _ _
  have hd1 : LaurentSeries.derivative F (formalY W ^ 2) =
      formalY W * LaurentSeries.derivative F (formalY W) +
        formalY W * LaurentSeries.derivative F (formalY W) := by
    rw [sq]; exact laurentSeries_derivative_mul _ _
  have hd2 : LaurentSeries.derivative F
      (HahnSeries.single (0 : ℤ) W.a₁ * formalX W * formalY W) =
      HahnSeries.single (0 : ℤ) W.a₁ * formalX W * LaurentSeries.derivative F (formalY W) +
        formalY W * (HahnSeries.single (0 : ℤ) W.a₁ * LaurentSeries.derivative F (formalX W)) := by
    rw [laurentSeries_derivative_mul (HahnSeries.single (0 : ℤ) W.a₁ * formalX W) (formalY W),
      laurentSeries_derivative_mul (HahnSeries.single (0 : ℤ) W.a₁) (formalX W),
      laurent_derivative_single_zero, mul_zero, add_zero]
  have hd3 : LaurentSeries.derivative F (HahnSeries.single (0 : ℤ) W.a₃ * formalY W) =
      HahnSeries.single (0 : ℤ) W.a₃ * LaurentSeries.derivative F (formalY W) := by
    rw [laurentSeries_derivative_mul, laurent_derivative_single_zero, mul_zero, add_zero]
  have hd4 : LaurentSeries.derivative F (formalX W ^ 3) =
      formalX W ^ 2 * LaurentSeries.derivative F (formalX W) +
        formalX W * (formalX W * LaurentSeries.derivative F (formalX W) +
          formalX W * LaurentSeries.derivative F (formalX W)) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ,
      laurentSeries_derivative_mul (formalX W ^ 2) (formalX W), hsq]
  have hd5 : LaurentSeries.derivative F (HahnSeries.single (0 : ℤ) W.a₂ * formalX W ^ 2) =
      HahnSeries.single (0 : ℤ) W.a₂ *
        (formalX W * LaurentSeries.derivative F (formalX W) +
          formalX W * LaurentSeries.derivative F (formalX W)) := by
    rw [laurentSeries_derivative_mul, laurent_derivative_single_zero, mul_zero, add_zero, hsq]
  have hd6 : LaurentSeries.derivative F (HahnSeries.single (0 : ℤ) W.a₄ * formalX W) =
      HahnSeries.single (0 : ℤ) W.a₄ * LaurentSeries.derivative F (formalX W) := by
    rw [laurentSeries_derivative_mul, laurent_derivative_single_zero, mul_zero, add_zero]
  rw [hd1, hd2, hd3, hd4, hd5, hd6, laurent_derivative_single_zero] at hD
  linear_combination hD

/-- **IV.4.3 sub-leaf (N): invariant-differential normalization** (Silverman IV.4.2, Prop. 4.2):
the local-`t`-expansion of `ω = u⁻¹ dx` has constant coefficient `1`. Concretely
`(localExpand u)⁻¹ · (d/dt)(localExpand x)` has `coeff 0 = 1` — the formal-group invariant
differential `ω_F(T) = 1 + O(T)` (cf. `FormalGroup.invariantDiff_constantCoeff`), here for the
expansions `localExpand x = formalX`, `localExpand u = 2·formalY + a₁·formalX + a₃`.

No `α` appears, so — unlike the chain-rule leaf (P) below — this statement needs **no**
genuineness guard (verified at the 2026-06-11 restatement pass): it is the IV.4.2
normalization for the curve's own expansions, true in every characteristic.

**Discharged (2026-06-11) by the direct Laurent computation, organized char-free in the
ratio**: if `2 ≠ 0`, both `u(t)` and `x′(t)` have `orderTop = −3` with leading coefficient
`−2`, so the ratio has `orderTop = 0` and leading (= constant) coefficient `(−2)⁻¹·(−2) = 1`.
If `2 = 0`, the leading `−2t⁻³` terms vanish *on both sides*; instead of dividing by `2`, the
implicit-differentiation identity `u·y′ = v·x′` (`formalXY_weierstrass_derivative`) rewrites
the ratio as `v⁻¹·y′` with `v = 3x² + 2a₂x + a₄ − a₁y`, and now both `v` and `y′` have
`orderTop = −4` with leading coefficient `3 = 1 ≠ 0` (char 2), so the constant coefficient is
again `3⁻¹·3 = 1`. -/
theorem invariantDiff_localExpand_coeff_zero :
    ((localExpand W (u_gen W))⁻¹ *
        LaurentSeries.derivative F (localExpand W (x_gen W))).coeff 0 = 1 := by
  classical
  rw [localExpand_x_gen, localExpand_u_gen]
  set XX := formalX W with hXX_def
  set YY := formalY W with hYY_def
  set DX := LaurentSeries.derivative F XX with hDX_def
  set DY := LaurentSeries.derivative F YY with hDY_def
  set u : LaurentSeries F := YY + YY + HahnSeries.single (0 : ℤ) W.a₁ * XX +
    HahnSeries.single (0 : ℤ) W.a₃ with hu_def
  -- coefficient facts for u
  have hu_coeff : ∀ j : ℤ, u.coeff j =
      YY.coeff j + YY.coeff j + W.a₁ * XX.coeff j +
        (HahnSeries.single (0 : ℤ) W.a₃).coeff j := by
    intro j
    simp only [hu_def, HahnSeries.coeff_add, HahnSeries.single_zero_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  have hu_lt : ∀ j : ℤ, j < -3 → u.coeff j = 0 := by
    intro j hj
    rw [hu_coeff, formalY_coeff_of_lt W hj, formalX_coeff_of_lt W (by omega),
      HahnSeries.coeff_single_of_ne (show j ≠ 0 by omega)]
    ring
  have hu_at : u.coeff (-3) = -(2 : F) := by
    rw [hu_coeff, formalY_coeff_neg_three, formalX_coeff_of_lt W (by norm_num),
      HahnSeries.coeff_single_of_ne (show (-3 : ℤ) ≠ 0 by norm_num)]
    ring
  -- derivative coefficient facts for DX
  have hDX_lt : ∀ j : ℤ, j < -3 → DX.coeff j = 0 := by
    intro j hj
    rw [hDX_def, laurent_derivative_coeff, formalX_coeff_of_lt W (by omega), smul_zero]
  have hDX_at : DX.coeff (-3) = -(2 : F) := by
    rw [hDX_def, laurent_derivative_coeff]
    norm_num [hXX_def, formalX_coeff_neg_two]
  by_cases h2 : (2 : F) = 0
  · -- char 2: switch to the y-form via the differentiated Weierstrass identity
    have hE := formalXY_weierstrass_derivative W
    rw [← hXX_def, ← hYY_def, ← hDX_def, ← hDY_def, ← hu_def] at hE
    set v : LaurentSeries F := XX ^ 2 + XX ^ 2 + XX ^ 2 +
      (HahnSeries.single (0 : ℤ) W.a₂ * XX + HahnSeries.single (0 : ℤ) W.a₂ * XX) +
      HahnSeries.single (0 : ℤ) W.a₄ - HahnSeries.single (0 : ℤ) W.a₁ * YY with hv_def
    have hv_coeff : ∀ j : ℤ, v.coeff j =
        (XX ^ 2).coeff j + (XX ^ 2).coeff j + (XX ^ 2).coeff j +
          (W.a₂ * XX.coeff j + W.a₂ * XX.coeff j) +
          (HahnSeries.single (0 : ℤ) W.a₄).coeff j - W.a₁ * YY.coeff j := by
      intro j
      simp only [hv_def, HahnSeries.coeff_sub, HahnSeries.coeff_add,
        HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    have hv_lt : ∀ j : ℤ, j < -4 → v.coeff j = 0 := by
      intro j hj
      rw [hv_coeff, formalX_sq_coeff_of_lt W hj, formalX_coeff_of_lt W (by omega),
        formalY_coeff_of_lt W (by omega),
        HahnSeries.coeff_single_of_ne (show j ≠ 0 by omega)]
      ring
    have hv_at : v.coeff (-4) = (3 : F) := by
      rw [hv_coeff, formalX_sq_coeff_neg_four, formalX_coeff_of_lt W (by norm_num),
        formalY_coeff_of_lt W (by norm_num),
        HahnSeries.coeff_single_of_ne (show (-4 : ℤ) ≠ 0 by norm_num)]
      ring
    have h3 : (3 : F) = 1 := by
      rw [show (3 : F) = 2 + 1 by norm_num, h2, zero_add]
    have hDY_lt : ∀ j : ℤ, j < -4 → DY.coeff j = 0 := by
      intro j hj
      rw [hDY_def, laurent_derivative_coeff, formalY_coeff_of_lt W (by omega), smul_zero]
    have hDY_at : DY.coeff (-4) = (3 : F) := by
      rw [hDY_def, laurent_derivative_coeff]
      norm_num [hYY_def, formalY_coeff_neg_three]
    have hv_ne0 : v.coeff (-4) ≠ 0 := by rw [hv_at, h3]; exact one_ne_zero
    have hv_ord : v.orderTop = ((-4 : ℤ) : WithTop ℤ) :=
      laurent_orderTop_eq_of_coeff hv_lt hv_ne0
    have hDY_ne0 : DY.coeff (-4) ≠ 0 := by rw [hDY_at, h3]; exact one_ne_zero
    have hDY_ord : DY.orderTop = ((-4 : ℤ) : WithTop ℤ) :=
      laurent_orderTop_eq_of_coeff hDY_lt hDY_ne0
    have hv_ne : v ≠ 0 := fun h ↦ hv_ne0 (by rw [h, HahnSeries.coeff_zero])
    -- u ≠ 0 via injectivity of localExpand (coefficientwise u is invisible in char 2)
    have hu_ne : u ≠ 0 := by
      rw [hu_def, ← localExpand_u_gen]
      intro h
      exact u_gen_ne_zero W (localExpand_injective W (by rw [h, map_zero]))
    -- swap to the y-form
    have hswap : u⁻¹ * DX = v⁻¹ * DY := by
      field_simp
      linear_combination -hE
    rw [hswap]
    have hord : (v⁻¹ * DY).orderTop = ((0 : ℤ) : WithTop ℤ) := by
      rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_inv_eq_neg hv_ne, hv_ord, hDY_ord]
      rfl
    rw [laurent_coeff_eq_leadingCoeff_of_orderTop hord, HahnSeries.leadingCoeff_mul,
      HahnSeries.leadingCoeff_inv hv_ne,
      ← laurent_coeff_eq_leadingCoeff_of_orderTop hv_ord,
      ← laurent_coeff_eq_leadingCoeff_of_orderTop hDY_ord, hv_at, hDY_at, h3]
    norm_num
  · -- char ≠ 2: direct computation on the x-form
    have hu_ne0 : u.coeff (-3) ≠ 0 := by
      rw [hu_at]; exact neg_ne_zero.mpr h2
    have hu_ord : u.orderTop = ((-3 : ℤ) : WithTop ℤ) :=
      laurent_orderTop_eq_of_coeff hu_lt hu_ne0
    have hDX_ne0 : DX.coeff (-3) ≠ 0 := by
      rw [hDX_at]; exact neg_ne_zero.mpr h2
    have hDX_ord : DX.orderTop = ((-3 : ℤ) : WithTop ℤ) :=
      laurent_orderTop_eq_of_coeff hDX_lt hDX_ne0
    have hu_ne : u ≠ 0 := fun h ↦ hu_ne0 (by rw [h, HahnSeries.coeff_zero])
    have hord : (u⁻¹ * DX).orderTop = ((0 : ℤ) : WithTop ℤ) := by
      rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_inv_eq_neg hu_ne, hu_ord, hDX_ord]
      rfl
    rw [laurent_coeff_eq_leadingCoeff_of_orderTop hord, HahnSeries.leadingCoeff_mul,
      HahnSeries.leadingCoeff_inv hu_ne,
      ← laurent_coeff_eq_leadingCoeff_of_orderTop hu_ord,
      ← laurent_coeff_eq_leadingCoeff_of_orderTop hDX_ord, hu_at, hDX_at]
    rw [inv_mul_cancel₀ (neg_ne_zero.mpr h2)]

/-- Rearrangement of the differentiated substituted fixed-point equation into the
quotient-rule numerator identity (abstract commutative-ring identity, because `ring`
cannot normalise `PowerSeries` goals in this toolchain): from the substituted fixed point
`v = f³ + a₁fv + a₂f²v + a₃v² + a₄fv² + a₆v³`, the substituted implicit-differentiation
identity `w′·(1 − f_w(f,v)) = f_z(f,v)`, and the chain rule `dv = w′·f′`, derive
`(f′v − f·dv)·(1 − f_w(f,v)) = f′·v·(a₁f + a₃v − 2)`. The right-hand factor
`a₁f + a₃v − 2` is exactly the `(z,w)`-chart expansion of `u·w` (`u = 2y + a₁x + a₃`,
`w = −1/y`), which is what cancels the `u`-denominator of the invariant differential —
uniformly in the characteristic (no division by `2` or `3` anywhere). -/
private lemma pullback_diff_rearrange {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ f v f' dv w' : A)
    (hfix : v = f ^ 3 + a₁ * f * v + a₂ * f ^ 2 * v + a₃ * v ^ 2 + a₄ * f * v ^ 2 + a₆ * v ^ 3)
    (hkey : w' * (1 - (a₁ * f + a₂ * f ^ 2 + 2 * (a₃ * v) + 2 * (a₄ * (f * v))
        + 3 * (a₆ * v ^ 2)))
      = 3 * f ^ 2 + a₁ * v + 2 * (a₂ * (f * v)) + a₄ * v ^ 2)
    (hchain : dv = w' * f') :
    (f' * v - f * dv)
        * (1 - (a₁ * f + a₂ * f ^ 2 + 2 * (a₃ * v) + 2 * (a₄ * (f * v)) + 3 * (a₆ * v ^ 2)))
      = f' * v * (a₁ * f + a₃ * v - 2) := by
  linear_combination (3 * f') * hfix - f * f' * hkey
    - ((1 - (a₁ * f + a₂ * f ^ 2 + 2 * (a₃ * v) + 2 * (a₄ * (f * v)) + 3 * (a₆ * v ^ 2))) * f)
      * hchain

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **The (P) core, chart-level form**: for a power series `f` with zero constant term and
Laurent series `xL` (the `x`-expansion) and `U` (the `u`-expansion) satisfying the two cleared
chart relations `xL·T = S` and `U·T = a₁·S + a₃·T − 2` (`S := ofPS f`, `T := ofPS (w∘f)` —
these are `x = z/w` and `u·w = a₁z + a₃w − 2` pushed through the expansions), the constant
coefficient of `U⁻¹·(d/dt) xL` is the linear coefficient of `f`.

The computation (uniform in the characteristic): differentiating `xL·T = S` gives
`xL·T′ + T·xL′ = S′`; the differentiated substituted fixed-point equation
(`pullback_diff_rearrange` fed by mathlib's chain rule `PowerSeries.derivative_subst` and
FG-B4a's `subst_derivative_formalW_key`) gives `(S′T − ST′)·(1 − P) = S′·T·(a₁S + a₃T − 2)`
with `P := f_w(f, w∘f)` of positive order; combining, `(U⁻¹·xL′)·(1 − P) = S′`. Since `1 − P`
is a unit of order `0`, `coeff₀ (U⁻¹·xL′) = coeff₀ S′ = coeff₁ f`. -/
theorem pullback_invariantDiff_core (f : PowerSeries F)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (xL U : LaurentSeries F)
    (hT_ne : HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ≠ 0)
    (hU_ne : U ≠ 0)
    (hxT : xL * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F f)
    (hUT : U * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * HahnSeries.ofPowerSeries ℤ F f
        + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
            * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) - 2) :
    (U⁻¹ * LaurentSeries.derivative F xL).coeff 0 =
      (HahnSeries.ofPowerSeries ℤ F f).coeff (1 : ℤ) := by
  classical
  have hford : 1 ≤ f.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf0
  have hfsub : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hv0 : PowerSeries.constantCoeff (PowerSeries.subst f (formalW W)) = 0 :=
    constantCoeff_subst_formalW W f hf0
  -- ## Power-series layer: fixed point, implicit differentiation, chain rule
  have hfix : PowerSeries.subst f (formalW W) = f ^ 3
      + PowerSeries.C W.a₁ * f * PowerSeries.subst f (formalW W)
      + PowerSeries.C W.a₂ * f ^ 2 * PowerSeries.subst f (formalW W)
      + PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W) ^ 2
      + PowerSeries.C W.a₄ * f * PowerSeries.subst f (formalW W) ^ 2
      + PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 3 :=
    subst_formalW_fixedPoint W f hford
  have hkey := subst_derivative_formalW_key W f hfsub
  have hchain : d⁄dX F (PowerSeries.subst f (formalW W)) =
      PowerSeries.subst f (d⁄dX F (formalW W)) * d⁄dX F f :=
    PowerSeries.derivative_subst hfsub
  have hstar := pullback_diff_rearrange (PowerSeries.C W.a₁) (PowerSeries.C W.a₂)
    (PowerSeries.C W.a₃) (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) f
    (PowerSeries.subst f (formalW W)) (d⁄dX F f)
    (d⁄dX F (PowerSeries.subst f (formalW W)))
    (PowerSeries.subst f (d⁄dX F (formalW W))) hfix hkey hchain
  -- ## Push to Laurent series along the ring hom `ofPowerSeries`
  have hstar_L := congrArg (HahnSeries.ofPowerSeries ℤ F) hstar
  -- `hstar` comes from applying `pullback_diff_rearrange`; its LHS product carries the `d⁄dX`
  -- coercions, which block `map_mul`/`map_sub` from firing under the default reducibility used
  -- by `simp`'s defeq matcher. Relaxing `respectTransparency` lets the ring hom fully distribute
  -- so the result shares atoms with the goal / `hDx` / `hxT` / `hUT` for the `linear_combination`.
  set_option backward.isDefEq.respectTransparency false in
  simp only [map_mul, map_sub, map_add, map_pow, map_one,
    show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
    show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3] at hstar_L
  -- the differentiated cleared chart relation `xL·T′ + T·xL′ = S′`
  have hDx := congrArg (LaurentSeries.derivative F) hxT
  rw [laurentSeries_derivative_mul, laurent_derivative_ofPowerSeries,
    laurent_derivative_ofPowerSeries] at hDx
  -- ## The order-`≥ 1` block `PL := ofPS (f_w(f, w∘f))` and its unit complement
  have hP0 : PowerSeries.constantCoeff
      (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
        + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
        + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
        + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)) = 0 := by
    simp [hf0, hv0]
  have hPL1 : (1 : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
        + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
        + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
        + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2))).orderTop :=
    laurent_ofPowerSeries_orderTop_one_le _ hP0
  have hPL_push : HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
        + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
        + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
        + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * HahnSeries.ofPowerSeries ℤ F f
        + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₂)
            * HahnSeries.ofPowerSeries ℤ F f ^ 2
        + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
            * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
        + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₄)
            * (HahnSeries.ofPowerSeries ℤ F f
                * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))))
        + 3 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₆)
            * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ^ 2) := by
    simp only [map_mul, map_add, map_pow,
      show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
      show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3]
  set PL : LaurentSeries F := HahnSeries.ofPowerSeries ℤ F
    (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
      + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
      + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
      + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)) with hPL_def
  have hPL_coeff0 : PL.coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) hPL1)
  have h1P_coeff0 : ((1 : LaurentSeries F) - PL).coeff 0 = 1 := by
    rw [HahnSeries.coeff_sub, hPL_coeff0, sub_zero, HahnSeries.coeff_one, if_pos rfl]
  have h1P_lt : ∀ j : ℤ, j < 0 → ((1 : LaurentSeries F) - PL).coeff j = 0 := by
    intro j hj
    rw [HahnSeries.coeff_sub, hPL_def, laurent_ofPowerSeries_coeff_neg _ hj,
      HahnSeries.coeff_one, if_neg (by omega), sub_zero]
  have h1P_ord : ((1 : LaurentSeries F) - PL).orderTop = ((0 : ℤ) : WithTop ℤ) :=
    laurent_orderTop_eq_of_coeff h1P_lt (by rw [h1P_coeff0]; exact one_ne_zero)
  have h1P_ne : (1 : LaurentSeries F) - PL ≠ 0 := fun h ↦
    one_ne_zero (by rw [← h1P_coeff0, h, HahnSeries.coeff_zero])
  -- ## The main multiplicative identity `(d/dt) xL · (1 − PL) = S′ · U`, T²-cleared
  have hDxU2 : LaurentSeries.derivative F xL * ((1 : LaurentSeries F) - PL)
        * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
      = HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) * U
        * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) := by
    -- `set` already folded the sum to `PL` in the goal; `hPL_push : PL = …` (also folded by
    -- `set`) pushes the ring hom over the sum into the per-`aᵢ` product spelling the
    -- `linear_combination` below is written against.
    rw [hPL_push]
    linear_combination
      (((1 : LaurentSeries F)
            - (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)
                  * HahnSeries.ofPowerSeries ℤ F f
              + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₂)
                  * HahnSeries.ofPowerSeries ℤ F f ^ 2
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₄)
                  * (HahnSeries.ofPowerSeries ℤ F f
                      * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))))
              + 3 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₆)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ^ 2)))
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) * hDx
      - (((1 : LaurentSeries F)
            - (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)
                  * HahnSeries.ofPowerSeries ℤ F f
              + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₂)
                  * HahnSeries.ofPowerSeries ℤ F f ^ 2
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₄)
                  * (HahnSeries.ofPowerSeries ℤ F f
                      * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))))
              + 3 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₆)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ^ 2)))
          * HahnSeries.ofPowerSeries ℤ F (d⁄dX F (PowerSeries.subst f (formalW W)))) * hxT
      + hstar_L
      - (HahnSeries.ofPowerSeries ℤ F (d⁄dX F f)
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) * hUT
  have hDxU : LaurentSeries.derivative F xL * ((1 : LaurentSeries F) - PL)
      = HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) * U :=
    mul_right_cancel₀ (mul_ne_zero hT_ne hT_ne) hDxU2
  -- ## Divide by the unit `U` and read off `coeff 0`
  have hMP : (U⁻¹ * LaurentSeries.derivative F xL) * ((1 : LaurentSeries F) - PL) =
      HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) := by
    rw [mul_assoc, hDxU, mul_comm _ U, ← mul_assoc, inv_mul_cancel₀ hU_ne, one_mul]
  have hM_eq : U⁻¹ * LaurentSeries.derivative F xL =
      HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) * ((1 : LaurentSeries F) - PL)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ h1P_ne).mpr hMP
  have h1Pinv_ord : (((1 : LaurentSeries F) - PL)⁻¹).orderTop = ((0 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.orderTop_inv_eq_neg h1P_ne, h1P_ord]
    rfl
  have hM_ord : (0 : WithTop ℤ) ≤ (U⁻¹ * LaurentSeries.derivative F xL).orderTop := by
    rw [hM_eq, HahnSeries.orderTop_mul, h1Pinv_ord,
      show ((0 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) from rfl, add_zero]
    exact laurent_ofPowerSeries_orderTop_nonneg _
  have hMPL0 : ((U⁻¹ * LaurentSeries.derivative F xL) * PL).coeff 0 = 0 := by
    refine HahnSeries.coeff_eq_zero_of_lt_orderTop ?_
    rw [HahnSeries.orderTop_mul]
    calc ((0 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ) + (1 : WithTop ℤ) := by
          rw [zero_add]; exact_mod_cast zero_lt_one
      _ ≤ _ := add_le_add hM_ord hPL1
  have hsplit : U⁻¹ * LaurentSeries.derivative F xL =
      HahnSeries.ofPowerSeries ℤ F (d⁄dX F f)
        + (U⁻¹ * LaurentSeries.derivative F xL) * PL := by
    linear_combination hMP
  have hc := congrArg (fun z : LaurentSeries F ↦ z.coeff 0) hsplit
  simp only [HahnSeries.coeff_add, hMPL0, add_zero] at hc
  rw [hc, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_derivative]
  norm_num

/-- **IV.4.3 sub-leaf (P): the chain rule for the pulled-back differential — PROVEN**
(Silverman IV.4.2/4.3): for a *genuine* isogeny, the constant coefficient of the
`t`-expansion of `α*ω = (α*u)⁻¹ d(α*x)` equals the linear coefficient of the `t`-expansion
of `α*t` (`= α.pullback localParam`). This is the formal-group identity
`ω_G(f(T))·f'(T) = a_f·ω_F(T)` read off at `T = 0` (`f'(0) = a_f`), transported to the
concrete `localExpand` expansions via the FG-B2 chart identities.

**Why the genuineness guard is the x-pole `h_α` and NOT the weaker
`0 < orderTop (localExpand (α*t))`** (re-restated 2026-06-11, closing FG-C4): the
`h_orderTop` form is still refutable. The project `Isogeny.pullback` is an unconstrained
`AlgHom`, so translation pullbacks `τ_S^*` qualify; for a translation by a point `S` with
`x(S) = 0`, `y(S) ≠ 0`, the pullback `τ_S^* t` *does* vanish at `O` (its expansion has
`orderTop = 1`), yet the LHS is the expansion of the translation-invariant `ω` itself
(constant coefficient `1`, by (N)) while the RHS is `⟨dt|_S, v_S⟩ = −(2y(S)+a₃)/y(S) ≠ 1`
generically (e.g. `= −2` for `S = (0,1)` on `y² = x³+x²+x+1`). This is the same missing
basepoint phenomenon as R5a (`ord_pullback_x_neg_of_localParam_pos`,
`FormalIsogenySeries.lean`): positive `t`-order does **not** force the `x`-pole. The pole
hypothesis `h_α` — the guard used throughout FG-B (`formalIsogenySeries_add`, the FG-B2
chart expansions) — restricts to expansion pairs through the formal disk at `O`, where the
identity is true uniformly in the characteristic; every concrete isogeny in the development
supplies it (e.g. `ordAtInfty_mulByInt_x_neg`).

Proof: the FG-B2 chart identities give the cleared relations `xL·T = S` and
`U·T = a₁S + a₃T − 2`; `pullback_invariantDiff_core` does the rest (mathlib's
`PowerSeries.derivative_subst` chain rule + FG-B4a's substituted implicit differentiation +
Laurent order bookkeeping). No characteristic split: the `−2` never gets divided by. -/
theorem pullback_invariantDiff_coeff_zero (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    ((localExpand W (alpha_star_u W α))⁻¹ *
        LaurentSeries.derivative F (localExpand W (α.pullback (x_gen W)))).coeff 0 =
      (localExpand W (α.pullback (localParam W))).coeff (1 : ℤ) := by
  classical
  -- genuineness: `f_α` has zero constant term
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α)
  -- nonvanishing: `T = ofPS (w ∘ f_α) ≠ 0` and `U = localExpand (α*u) ≠ 0`
  have hT_ne : HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) ≠ 0 := by
    intro h
    exact subst_formalIsogenySeries_formalW_ne_zero W α h_α
      (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  have hU_ne : localExpand W (alpha_star_u W α) ≠ 0 := by
    intro h
    apply u_gen_ne_zero W
    apply α.pullback_injective
    rw [map_zero, ← alpha_star_u_eq]
    exact localExpand_injective W (by rw [h, map_zero])
  -- cleared chart relation `xL·T = S` (FG-B2 x-leg)
  have hxT : localExpand W (α.pullback (x_gen W)) *
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α) := by
    rw [localExpand_pullback_x_gen W α h_α, div_mul_cancel₀ _ hT_ne]
  -- cleared chart relation `U·T = a₁·S + a₃·T − 2` (FG-B2 y-leg + `alpha_star_u`'s shape)
  have hTinv : (HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.subst (formalIsogenySeries W α) (formalW W)))⁻¹ *
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) = 1 :=
    inv_mul_cancel₀ hT_ne
  have hu_def : alpha_star_u W α = 2 * α.pullback (y_gen W)
      + algebraMap F KE W.a₁ * α.pullback (x_gen W) + algebraMap F KE W.a₃ := rfl
  have hUT : localExpand W (alpha_star_u W α) *
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)
          * HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α)
        + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
            * HahnSeries.ofPowerSeries ℤ F
                (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) - 2 := by
    rw [hu_def, map_add, map_add, map_mul, map_mul, map_ofNat, localExpand_algebraMap,
      localExpand_algebraMap, localExpand_pullback_y_gen W α h_α]
    linear_combination HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * hxT - 2 * hTinv
  rw [localExpand_pullback_localParam W α h_α]
  exact pullback_invariantDiff_core W (formalIsogenySeries W α) hf0 _ _ hT_ne hU_ne hxT hUT

/-- **L-KL-main sub-leaf (B), Silverman IV.4.3**: for a genuine isogeny (`h_orderTop`, threaded
to the chain-rule leaf (P)), the constant value of `a_α` equals the linear coefficient of the
formal isogeny series. Applies the `localExpand`-Kähler lift (`localExpandKaehlerLift`) to
`omegaPullbackCoeff_spec` (turning the Kähler identity `a_α • ω = (α*u)⁻¹ • D(α*x)` into a
Laurent-series identity), then reads off `coeff 0` using the normalization
`invariantDiff_localExpand_coeff_zero` (N) and the chain rule
`pullback_invariantDiff_coeff_zero` (P). -/
theorem omegaPullbackCoeff_F_value_eq_coeff_one
    (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (c : F) (hc : omegaPullbackCoeff W α = algebraMap F KE c) :
    c = PowerSeries.coeff 1 (formalIsogenySeries W α) := by
  rw [formalIsogenySeries_coeff, Nat.cast_one]
  have hspec := omegaPullbackCoeff_spec W α
  rw [show algebraMap W.toAffine.CoordinateRing KE
        (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) = x_gen W from
      rfl] at hspec
  have hKI := congrArg (fun ω ↦ (localExpandKaehlerLift W ω).out) hspec
  simp only [localExpandKaehlerLift_smul] at hKI
  have hω : (localExpandKaehlerLift W (invariantDifferential W.toAffine)).out =
      (localExpand W (u_gen W))⁻¹ * LaurentSeries.derivative F (localExpand W (x_gen W)) := by
    show (localExpandKaehlerLift W ((u_gen W)⁻¹ • KaehlerDifferential.D F KE (x_gen W))).out = _
    rw [localExpandKaehlerLift_smul, localExpandKaehlerLift_D, map_inv₀]
  rw [hc, hω, localExpandKaehlerLift_D, map_inv₀] at hKI
  have hc0 := congrArg (fun s ↦ HahnSeries.coeff s 0) hKI
  simp only [pullback_invariantDiff_coeff_zero W α h_α] at hc0
  rw [← hc0, localExpand_algebraMap, HahnSeries.ofPowerSeries_C,
    show (HahnSeries.C c : LaurentSeries F) = HahnSeries.single 0 c from rfl,
    HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul,
    invariantDiff_localExpand_coeff_zero W, smul_eq_mul, mul_one]

end HasseWeil

open HasseWeil WeierstrassCurve PowerSeries

namespace HasseWeil.OmegaRegularityProof

variable {F : Type*} [Field F]

private lemma pullback_diff_rearrange {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ f v f' dv w' : A)
    (hfix : v = f ^ 3 + a₁ * f * v + a₂ * f ^ 2 * v + a₃ * v ^ 2 + a₄ * f * v ^ 2 + a₆ * v ^ 3)
    (hkey : w' * (1 - (a₁ * f + a₂ * f ^ 2 + 2 * (a₃ * v) + 2 * (a₄ * (f * v))
        + 3 * (a₆ * v ^ 2)))
      = 3 * f ^ 2 + a₁ * v + 2 * (a₂ * (f * v)) + a₄ * v ^ 2)
    (hchain : dv = w' * f') :
    (f' * v - f * dv)
        * (1 - (a₁ * f + a₂ * f ^ 2 + 2 * (a₃ * v) + 2 * (a₄ * (f * v)) + 3 * (a₆ * v ^ 2)))
      = f' * v * (a₁ * f + a₃ * v - 2) := by
  linear_combination (3 * f') * hfix - f * f' * hkey
    - ((1 - (a₁ * f + a₂ * f ^ 2 + 2 * (a₃ * v) + 2 * (a₄ * (f * v)) + 3 * (a₆ * v ^ 2))) * f)
      * hchain

variable (W : WeierstrassCurve F)

theorem pullback_invariantDiff_core_nonneg (f : PowerSeries F)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (xL U : LaurentSeries F)
    (hT_ne : HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ≠ 0)
    (hU_ne : U ≠ 0)
    (hxT : xL * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F f)
    (hUT : U * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * HahnSeries.ofPowerSeries ℤ F f
        + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
            * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) - 2) :
    (0 : WithTop ℤ) ≤ (U⁻¹ * LaurentSeries.derivative F xL).orderTop := by
  classical
  have hford : 1 ≤ f.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf0
  have hfsub : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hv0 : PowerSeries.constantCoeff (PowerSeries.subst f (formalW W)) = 0 :=
    constantCoeff_subst_formalW W f hf0
  have hfix : PowerSeries.subst f (formalW W) = f ^ 3
      + PowerSeries.C W.a₁ * f * PowerSeries.subst f (formalW W)
      + PowerSeries.C W.a₂ * f ^ 2 * PowerSeries.subst f (formalW W)
      + PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W) ^ 2
      + PowerSeries.C W.a₄ * f * PowerSeries.subst f (formalW W) ^ 2
      + PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 3 :=
    subst_formalW_fixedPoint W f hford
  have hkey := subst_derivative_formalW_key W f hfsub
  have hchain : d⁄dX F (PowerSeries.subst f (formalW W)) =
      PowerSeries.subst f (d⁄dX F (formalW W)) * d⁄dX F f :=
    PowerSeries.derivative_subst hfsub
  have hstar := pullback_diff_rearrange (PowerSeries.C W.a₁) (PowerSeries.C W.a₂)
    (PowerSeries.C W.a₃) (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) f
    (PowerSeries.subst f (formalW W)) (d⁄dX F f)
    (d⁄dX F (PowerSeries.subst f (formalW W)))
    (PowerSeries.subst f (d⁄dX F (formalW W))) hfix hkey hchain
  have hstar_L := congrArg (HahnSeries.ofPowerSeries ℤ F) hstar
  simp only [map_mul, map_sub, map_add, map_pow, map_one,
    show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
    show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3] at hstar_L
  have hDx := congrArg (LaurentSeries.derivative F) hxT
  rw [laurentSeries_derivative_mul, laurent_derivative_ofPowerSeries,
    laurent_derivative_ofPowerSeries] at hDx
  have hP0 : PowerSeries.constantCoeff
      (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
        + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
        + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
        + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)) = 0 := by
    simp [hf0, hv0]
  have hPL1 : (1 : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
        + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
        + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
        + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2))).orderTop :=
    laurent_ofPowerSeries_orderTop_one_le _ hP0
  have hPL_push : HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
        + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
        + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
        + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * HahnSeries.ofPowerSeries ℤ F f
        + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₂)
            * HahnSeries.ofPowerSeries ℤ F f ^ 2
        + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
            * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
        + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₄)
            * (HahnSeries.ofPowerSeries ℤ F f
                * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))))
        + 3 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₆)
            * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ^ 2) := by
    simp only [map_mul, map_add, map_pow,
      show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
      show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3]
  set PL : LaurentSeries F := HahnSeries.ofPowerSeries ℤ F
    (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
      + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
      + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
      + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)) with hPL_def
  have hPL_coeff0 : PL.coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) hPL1)
  have h1P_coeff0 : ((1 : LaurentSeries F) - PL).coeff 0 = 1 := by
    rw [HahnSeries.coeff_sub, hPL_coeff0, sub_zero, HahnSeries.coeff_one, if_pos rfl]
  have h1P_lt : ∀ j : ℤ, j < 0 → ((1 : LaurentSeries F) - PL).coeff j = 0 := by
    intro j hj
    rw [HahnSeries.coeff_sub, hPL_def, laurent_ofPowerSeries_coeff_neg _ hj,
      HahnSeries.coeff_one, if_neg (by omega), sub_zero]
  have h1P_ord : ((1 : LaurentSeries F) - PL).orderTop = ((0 : ℤ) : WithTop ℤ) :=
    laurent_orderTop_eq_of_coeff h1P_lt (by rw [h1P_coeff0]; exact one_ne_zero)
  have h1P_ne : (1 : LaurentSeries F) - PL ≠ 0 := fun h ↦
    one_ne_zero (by rw [← h1P_coeff0, h, HahnSeries.coeff_zero])
  have hDxU2 : LaurentSeries.derivative F xL * ((1 : LaurentSeries F) - PL)
        * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
      = HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) * U
        * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) := by
    rw [hPL_push]
    linear_combination
      (((1 : LaurentSeries F)
            - (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)
                  * HahnSeries.ofPowerSeries ℤ F f
              + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₂)
                  * HahnSeries.ofPowerSeries ℤ F f ^ 2
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₄)
                  * (HahnSeries.ofPowerSeries ℤ F f
                      * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))))
              + 3 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₆)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ^ 2)))
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) * hDx
      - (((1 : LaurentSeries F)
            - (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)
                  * HahnSeries.ofPowerSeries ℤ F f
              + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₂)
                  * HahnSeries.ofPowerSeries ℤ F f ^ 2
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
              + 2 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₄)
                  * (HahnSeries.ofPowerSeries ℤ F f
                      * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))))
              + 3 * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₆)
                  * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ^ 2)))
          * HahnSeries.ofPowerSeries ℤ F (d⁄dX F (PowerSeries.subst f (formalW W)))) * hxT
      + hstar_L
      - (HahnSeries.ofPowerSeries ℤ F (d⁄dX F f)
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) * hUT
  have hDxU : LaurentSeries.derivative F xL * ((1 : LaurentSeries F) - PL)
      = HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) * U :=
    mul_right_cancel₀ (mul_ne_zero hT_ne hT_ne) hDxU2
  have hMP : (U⁻¹ * LaurentSeries.derivative F xL) * ((1 : LaurentSeries F) - PL) =
      HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) := by
    rw [mul_assoc, hDxU, mul_comm _ U, ← mul_assoc, inv_mul_cancel₀ hU_ne, one_mul]
  have hM_eq : U⁻¹ * LaurentSeries.derivative F xL =
      HahnSeries.ofPowerSeries ℤ F (d⁄dX F f) * ((1 : LaurentSeries F) - PL)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ h1P_ne).mpr hMP
  have h1Pinv_ord : (((1 : LaurentSeries F) - PL)⁻¹).orderTop = ((0 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.orderTop_inv_eq_neg h1P_ne, h1P_ord]
    rfl
  have hM_ord : (0 : WithTop ℤ) ≤ (U⁻¹ * LaurentSeries.derivative F xL).orderTop := by
    rw [hM_eq, HahnSeries.orderTop_mul, h1Pinv_ord,
      show ((0 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) from rfl, add_zero]
    exact laurent_ofPowerSeries_orderTop_nonneg _
  exact hM_ord

variable [DecidableEq F] [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

theorem pullback_invariantDiff_nonneg_of_x_pole (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    (0 : WithTop ℤ) ≤ ((localExpand W (alpha_star_u W α))⁻¹ *
      LaurentSeries.derivative F (localExpand W (α.pullback (x_gen W)))).orderTop := by
  classical
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α)
  have hT_ne : HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) ≠ 0 := by
    intro h
    exact subst_formalIsogenySeries_formalW_ne_zero W α h_α
      (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  have hU_ne : localExpand W (alpha_star_u W α) ≠ 0 := by
    intro h
    apply u_gen_ne_zero W
    apply α.pullback_injective
    rw [map_zero, ← alpha_star_u_eq]
    exact localExpand_injective W (by rw [h, map_zero])
  have hxT : localExpand W (α.pullback (x_gen W)) *
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α) := by
    rw [localExpand_pullback_x_gen W α h_α, div_mul_cancel₀ _ hT_ne]
  have hTinv : (HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.subst (formalIsogenySeries W α) (formalW W)))⁻¹ *
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) = 1 :=
    inv_mul_cancel₀ hT_ne
  have hu_def : alpha_star_u W α = 2 * α.pullback (y_gen W)
      + algebraMap F KE W.a₁ * α.pullback (x_gen W) + algebraMap F KE W.a₃ := rfl
  have hUT : localExpand W (alpha_star_u W α) *
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)
          * HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α)
        + HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
            * HahnSeries.ofPowerSeries ℤ F
                (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) - 2 := by
    rw [hu_def, map_add, map_add, map_mul, map_mul, map_ofNat, localExpand_algebraMap,
      localExpand_algebraMap, localExpand_pullback_y_gen W α h_α]
    linear_combination HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * hxT - 2 * hTinv
  exact pullback_invariantDiff_core_nonneg W (formalIsogenySeries W α) hf0 _ _ hT_ne hU_ne hxT hUT


omit [DecidableEq F] in
private theorem laurent_nonneg_add {a b : LaurentSeries F}
    (ha : (0 : WithTop ℤ) ≤ a.orderTop) (hb : (0 : WithTop ℤ) ≤ b.orderTop) :
    (0 : WithTop ℤ) ≤ (a + b).orderTop :=
  (le_min ha hb).trans HahnSeries.min_orderTop_le_orderTop_add

omit [DecidableEq F] in
private theorem laurent_nonneg_mul {a b : LaurentSeries F}
    (ha : (0 : WithTop ℤ) ≤ a.orderTop) (hb : (0 : WithTop ℤ) ≤ b.orderTop) :
    (0 : WithTop ℤ) ≤ (a * b).orderTop := by
  rw [HahnSeries.orderTop_mul]
  exact add_nonneg ha hb

omit [DecidableEq F] in
private theorem laurent_nonneg_pow {a : LaurentSeries F}
    (ha : (0 : WithTop ℤ) ≤ a.orderTop) (n : ℕ) :
    (0 : WithTop ℤ) ≤ (a ^ n).orderTop := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact laurent_nonneg_mul ih ha

omit [DecidableEq F] in
private theorem laurent_derivative_nonneg {a : LaurentSeries F}
    (ha : (0 : WithTop ℤ) ≤ a.orderTop) :
    (0 : WithTop ℤ) ≤ (LaurentSeries.derivative F a).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  rw [laurent_derivative_coeff]
  have hjneg : j < 0 := by exact_mod_cast hj
  by_cases hj1 : j + 1 = 0
  · rw [hj1, zero_smul]
  · rw [HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast (show j + 1 < 0 by omega)) ha), smul_zero]

omit [DecidableEq F] in
private theorem laurent_exists_powerSeries_of_nonneg {a : LaurentSeries F}
    (ha : (0 : WithTop ℤ) ≤ a.orderTop) :
    ∃ f : PowerSeries F, HahnSeries.ofPowerSeries ℤ F f = a := by
  refine ⟨PowerSeries.mk (fun n ↦ a.coeff (n : ℤ)), ?_⟩
  ext j
  by_cases hj : j < 0
  · rw [laurent_ofPowerSeries_coeff_neg _ hj,
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (lt_of_lt_of_le (by exact_mod_cast hj) ha)]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hj)
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

omit [DecidableEq F] in
private theorem laurent_quadratic_nonneg {b c y : LaurentSeries F}
    (hb : (0 : WithTop ℤ) ≤ b.orderTop) (hc : (0 : WithTop ℤ) ≤ c.orderTop)
    (h : y ^ 2 + b * y = c) : (0 : WithTop ℤ) ≤ y.orderTop := by
  by_contra! hy
  obtain ⟨n, hn⟩ : ∃ n : ℤ, y.orderTop = (n : WithTop ℤ) := by
    cases heq : y.orderTop with
    | top => simp [heq] at hy
    | coe n => exact ⟨n, rfl⟩
  have hnneg : n < 0 := by rw [hn] at hy; exact_mod_cast hy
  have hby : (n : WithTop ℤ) ≤ (b * y).orderTop := by
    rw [HahnSeries.orderTop_mul, hn]
    simpa only [zero_add] using add_le_add hb (le_refl (n : WithTop ℤ))
  have hy2 : (y ^ 2).orderTop = ((2 * n : ℤ) : WithTop ℤ) := by
    rw [sq, HahnSeries.orderTop_mul, hn]
    exact_mod_cast (show n + n = 2 * n by omega)
  have hleft : (y ^ 2 + b * y).orderTop = ((2 * n : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.orderTop_add_eq_left (hy2 ▸
      lt_of_lt_of_le (by exact_mod_cast (show 2 * n < n by omega)) hby), hy2]
  rw [h] at hleft
  rw [hleft] at hc
  have : 0 ≤ 2 * n := by exact_mod_cast hc
  omega

private theorem invariantDiff_localExpand_orderTop_zero :
    ((localExpand W (u_gen W))⁻¹ *
      LaurentSeries.derivative F (localExpand W (x_gen W))).orderTop = (0 : ℤ) := by
  have hnonneg := pullback_invariantDiff_nonneg_of_x_pole W (Isogeny.id W.toAffine)
    (by simpa using (show (W_smooth W).ordAtInfty (x_gen W) < 0 by
      rw [ordAtInfty_x_gen]; exact_mod_cast (show (-2 : ℤ) < 0 by decide)))
  have hnonneg' : (0 : WithTop ℤ) ≤ ((localExpand W (u_gen W))⁻¹ *
      LaurentSeries.derivative F (localExpand W (x_gen W))).orderTop := by
    simpa [alpha_star_u_eq] using hnonneg
  apply laurent_orderTop_eq_of_coeff
  · intro j hj
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast hj) hnonneg')
  · rw [invariantDiff_localExpand_coeff_zero W]
    exact one_ne_zero

private theorem localExpand_omega_lift :
    (localExpandKaehlerLift W (invariantDifferential W.toAffine)).out =
      (localExpand W (u_gen W))⁻¹ * LaurentSeries.derivative F (localExpand W (x_gen W)) := by
  change (localExpandKaehlerLift W
    ((u_gen W)⁻¹ • KaehlerDifferential.D F KE (x_gen W))).out = _
  rw [localExpandKaehlerLift_smul, localExpandKaehlerLift_D, map_inv₀]

private theorem omega_order_nonneg_of_unit_factor (a d : LaurentSeries F)
    (ha : a.orderTop = (0 : ℤ))
    (hd : (0 : WithTop ℤ) ≤ d.orderTop)
    (f : KE) (heq : d = a * localExpand W f *
      (localExpandKaehlerLift W (invariantDifferential W.toAffine)).out) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty f := by
  rw [heq, HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, ha,
    localExpand_omega_lift W, invariantDiff_localExpand_orderTop_zero W,
    show ((0 : ℤ) : WithTop ℤ) = 0 from rfl, zero_add, add_zero,
    orderTop_localExpand_eq_ordAtInfty W] at hd
  exact hd

private theorem omega_order_nonneg_of_x_pole (α : Isogeny W.toAffine W.toAffine)
    (hα : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (omegaPullbackCoeff W α) := by
  have hnonneg := pullback_invariantDiff_nonneg_of_x_pole W α hα
  have hspec := omegaPullbackCoeff_spec W α
  change omegaPullbackCoeff W α • invariantDifferential W.toAffine =
    (alpha_star_u W α)⁻¹ • KaehlerDifferential.D F KE (α.pullback (x_gen W)) at hspec
  have hKI := congrArg (fun ω ↦ (localExpandKaehlerLift W ω).out) hspec
  simp only [localExpandKaehlerLift_smul, localExpandKaehlerLift_D, map_inv₀] at hKI
  rw [← hKI, HahnSeries.orderTop_mul, localExpand_omega_lift W,
    invariantDiff_localExpand_orderTop_zero W,
    show ((0 : ℤ) : WithTop ℤ) = 0 from rfl, add_zero,
    orderTop_localExpand_eq_ordAtInfty W] at hnonneg
  exact hnonneg

omit [DecidableEq F] in
private theorem ofPowerSeries_orderTop_zero_of_constant {f : PowerSeries F}
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ F f).orderTop = (0 : ℤ) := by
  apply laurent_orderTop_eq_of_coeff
  · intro j hj
    exact laurent_ofPowerSeries_coeff_neg f hj
  · change (HahnSeries.ofPowerSeries ℤ F f).coeff ((0 : ℕ) : ℤ) ≠ 0
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hf

private theorem omega_order_nonneg_of_x_nonneg (α : Isogeny W.toAffine W.toAffine)
    (hα : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (α.pullback (x_gen W))) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (omegaPullbackCoeff W α) := by
  let x := localExpand W (α.pullback (x_gen W))
  let y := localExpand W (α.pullback (y_gen W))
  let c : F → LaurentSeries F := fun a ↦ HahnSeries.ofPowerSeries ℤ F (PowerSeries.C a)
  have hc (a : F) : (0 : WithTop ℤ) ≤ (c a).orderTop :=
    laurent_ofPowerSeries_orderTop_nonneg _
  have hx : (0 : WithTop ℤ) ≤ x.orderTop := by
    simpa only [x, orderTop_localExpand_eq_ordAtInfty W] using hα
  have heq : y ^ 2 + c W.a₁ * x * y + c W.a₃ * y =
      x ^ 3 + c W.a₂ * x ^ 2 + c W.a₄ * x + c W.a₆ := by
    have heq := pullback_equation_inl W α
    rw [Affine.equation_iff] at heq
    change (α.pullback (y_gen W)) ^ 2 +
      algebraMap F W.toAffine.FunctionField W.a₁ * α.pullback (x_gen W) * α.pullback (y_gen W) +
        algebraMap F W.toAffine.FunctionField W.a₃ * α.pullback (y_gen W) =
      (α.pullback (x_gen W)) ^ 3 +
        algebraMap F W.toAffine.FunctionField W.a₂ * (α.pullback (x_gen W)) ^ 2 +
          algebraMap F W.toAffine.FunctionField W.a₄ * α.pullback (x_gen W) +
            algebraMap F W.toAffine.FunctionField W.a₆ at heq
    have heqL := congrArg (localExpand W) heq
    change localExpand W (α.pullback (y_gen W)) ^ 2 +
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁)) * localExpand W (α.pullback (x_gen W)) *
        localExpand W (α.pullback (y_gen W)) +
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)) * localExpand W (α.pullback (y_gen W)) = _
    simpa only [map_add, map_mul, map_pow, localExpand_algebraMap] using heqL
  have hy : (0 : WithTop ℤ) ≤ y.orderTop := by
    apply laurent_quadratic_nonneg
      (laurent_nonneg_add (laurent_nonneg_mul (hc W.a₁) hx) (hc W.a₃))
      (laurent_nonneg_add
        (laurent_nonneg_add
          (laurent_nonneg_add (laurent_nonneg_pow hx 3)
            (laurent_nonneg_mul (hc W.a₂) (laurent_nonneg_pow hx 2)))
          (laurent_nonneg_mul (hc W.a₄) hx)) (hc W.a₆))
    linear_combination heq
  obtain ⟨xp, hxp⟩ := laurent_exists_powerSeries_of_nonneg hx
  obtain ⟨yp, hyp⟩ := laurent_exists_powerSeries_of_nonneg hy
  have hps : yp ^ 2 + PowerSeries.C W.a₁ * xp * yp + PowerSeries.C W.a₃ * yp =
      xp ^ 3 + PowerSeries.C W.a₂ * xp ^ 2 + PowerSeries.C W.a₄ * xp +
        PowerSeries.C W.a₆ := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_add, map_mul, map_pow, hxp, hyp] using heq
  have hconst := congrArg PowerSeries.constantCoeff hps
  simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_C] at hconst
  have hns : W.toAffine.Nonsingular (PowerSeries.constantCoeff xp)
      (PowerSeries.constantCoeff yp) :=
    W.toAffine.equation_iff_nonsingular.mp ((W.toAffine.equation_iff _ _).mpr hconst)
  rw [Affine.nonsingular_iff'] at hns
  let up := 2 * yp + PowerSeries.C W.a₁ * xp + PowerSeries.C W.a₃
  let vp := 3 * xp ^ 2 + 2 * PowerSeries.C W.a₂ * xp + PowerSeries.C W.a₄ -
    PowerSeries.C W.a₁ * yp
  have hu : HahnSeries.ofPowerSeries ℤ F up = localExpand W (alpha_star_u W α) := by
    simp only [up, map_add, map_mul, map_ofNat, hxp, hyp, alpha_star_u,
      localExpand_algebraMap]
    rfl
  have hv : HahnSeries.ofPowerSeries ℤ F vp = localExpand W
      (3 * (α.pullback (x_gen W)) ^ 2 +
        2 * algebraMap F KE W.a₂ * α.pullback (x_gen W) + algebraMap F KE W.a₄ -
        algebraMap F KE W.a₁ * α.pullback (y_gen W)) := by
    simp only [vp, map_sub, map_add, map_mul, map_pow, map_ofNat, hxp, hyp,
      localExpand_algebraMap]
    rfl
  rcases hns.2 with hV | hU
  · have hv0 : PowerSeries.constantCoeff vp ≠ 0 := by
      intro hv0
      apply hV
      simp only [vp, map_sub, map_add, map_mul, map_pow, map_ofNat,
        PowerSeries.constantCoeff_C] at hv0
      linear_combination -hv0
    have hDY := congrArg (fun ω ↦ (localExpandKaehlerLift W ω).out)
      (kaehler_D_alpha_pullback_y_eq_smul_omega W α)
    simp only [localExpandKaehlerLift_D, localExpandKaehlerLift_smul, map_mul] at hDY
    rw [← hv] at hDY
    exact omega_order_nonneg_of_unit_factor W _ _
      (ofPowerSeries_orderTop_zero_of_constant hv0) (laurent_derivative_nonneg hy) _ hDY
  · have hu0 : PowerSeries.constantCoeff up ≠ 0 := by
      simpa only [up, map_add, map_mul, map_ofNat, PowerSeries.constantCoeff_C] using hU
    have hDX := congrArg (fun ω ↦ (localExpandKaehlerLift W ω).out)
      (kaehler_D_alpha_pullback_x_eq_smul_omega W α)
    simp only [localExpandKaehlerLift_D, localExpandKaehlerLift_smul, map_mul] at hDX
    rw [← hu] at hDX
    exact omega_order_nonneg_of_unit_factor W _ _
      (ofPowerSeries_orderTop_zero_of_constant hu0) (laurent_derivative_nonneg hx) _ hDX

theorem omegaPullbackCoeff_ordAtInfty_nonneg_proof
    (α : Isogeny W.toAffine W.toAffine) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (omegaPullbackCoeff W α) := by
  by_cases hα : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0
  · exact omega_order_nonneg_of_x_pole W α hα
  · exact omega_order_nonneg_of_x_nonneg W α (le_of_not_gt hα)


end HasseWeil.OmegaRegularityProof

open WeierstrassCurve HasseWeil HasseWeil.Curves
open scoped TensorProduct

namespace HasseWeil.OmegaBaseChangeProof

section Compat
variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)
variable (L : Type*) [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]

noncomputable def tensorFunctionFieldEquiv :
    letI := C.isDomain_tensorCoordRing L
    (L ⊗[F] C.toAffine.FunctionField) ≃ₐ[L] (C.baseChange L).toAffine.FunctionField :=
  letI := C.isDomain_tensorCoordRing L
  (C.functionField_tensor_locBaseChange L).trans (C.functionField_baseChange_fracEquiv L)

/-- **The `L`-linear scalar extension `id_L ⊗ f`** of an `F`-algebra hom `f : K(C) →ₐ[F] K(C)`:
`Algebra.TensorProduct.map (AlgHom.id L) f : (L ⊗_F K(C)) →ₐ[L] (L ⊗_F K(C))`.  It is `L`-linear by
`Algebra.TensorProduct.map` (the left factor is the `L`-algebra identity). -/
noncomputable def lTensorMap (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    (L ⊗[F] C.toAffine.FunctionField) →ₐ[L] (L ⊗[F] C.toAffine.FunctionField) :=
  Algebra.TensorProduct.map (AlgHom.id L L) f

omit [Algebra.IsAlgebraic F L] in
@[simp] theorem lTensorMap_tmul
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) (l : L)
    (u : C.toAffine.FunctionField) :
    lTensorMap C L f (l ⊗ₜ u) = l ⊗ₜ f u := by
  simp [lTensorMap]

/-- **The base-changed pullback** `baseChangePullback f : K(C_L) →ₐ[L] K(C_L)`, the conjugate
`Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹` of the scalar extension `id_L ⊗ f` by the function-field iso `Φ`.

This is the honest base-change of the function-field hom `f` along `F → L`, requiring **no**
`CoordHom`.  It is an `L`-algebra hom by construction (composite of `L`-algebra homs). -/
noncomputable def baseChangePullback
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    (C.baseChange L).toAffine.FunctionField →ₐ[L] (C.baseChange L).toAffine.FunctionField :=
  letI := C.isDomain_tensorCoordRing L
  (tensorFunctionFieldEquiv C L).toAlgHom.comp
    ((lTensorMap C L f).comp (tensorFunctionFieldEquiv C L).symm.toAlgHom)

theorem baseChangePullback_apply
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField)
    (z : (C.baseChange L).toAffine.FunctionField) :
    baseChangePullback C L f z =
      tensorFunctionFieldEquiv C L (lTensorMap C L f
        ((tensorFunctionFieldEquiv C L).symm z)) :=
  rfl

theorem tensorFunctionFieldEquiv_one_tmul (z : C.toAffine.FunctionField) :
    letI := C.isDomain_tensorCoordRing L
    tensorFunctionFieldEquiv C L (1 ⊗ₜ[F] z) = C.functionFieldMap L z := by
  let := C.isDomain_tensorCoordRing L
  have hrh : ((tensorFunctionFieldEquiv C L).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := F) (A := L)
          (B := C.toAffine.FunctionField)).toRingHom) =
      (C.functionFieldMap L) := by
    refine IsFractionRing.ringHom_ext (A := C.toAffine.CoordinateRing) ?_
    intro u
    rw [RingHom.comp_apply]
    rw [C.functionFieldMap_algebraMap L u]
    change tensorFunctionFieldEquiv C L
        (Algebra.TensorProduct.includeRight
          (algebraMap C.toAffine.CoordinateRing C.toAffine.FunctionField u)) = _
    rw [Algebra.TensorProduct.includeRight_apply]
    have hstruct : (1 : L) ⊗ₜ[F]
          (algebraMap C.toAffine.CoordinateRing C.toAffine.FunctionField u) =
        C.tensorFunctionFieldStructureHom L (1 ⊗ₜ[F] u) := by
      change _ = Algebra.TensorProduct.map (AlgHom.id L L)
        (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField) (1 ⊗ₜ[F] u)
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [hstruct]
    let := C.tensorFunctionFieldAlgebra L
    let : IsScalarTower L (L ⊗[F] C.toAffine.CoordinateRing)
        (L ⊗[F] C.toAffine.FunctionField) :=
      IsScalarTower.of_algebraMap_eq fun l ↦
        ((C.tensorFunctionFieldStructureHom L).commutes l).symm
    have halg : C.tensorFunctionFieldStructureHom L (1 ⊗ₜ[F] u) =
        algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)
           (1 ⊗ₜ[F] u) := rfl
    rw [halg]
    change (C.functionField_baseChange_fracEquiv L)
        (C.functionField_tensor_locBaseChange L
          (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)
            (1 ⊗ₜ[F] u))) = _
    rw [show C.functionField_tensor_locBaseChange L
          (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)
            (1 ⊗ₜ[F] u)) =
        algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
          (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) (1 ⊗ₜ[F] u) from ?_]
    · rw [show C.functionField_baseChange_fracEquiv L =
            IsFractionRing.algEquivOfAlgEquiv (C.coordRingScalarExtPinned L) from rfl]
      rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
      congr 1
      change C.fwdPinned L (1 ⊗ₜ[F] u) = C.coordRingMap L u
      rw [C.fwdPinned_tmul, one_smul]
    · have := C.tensor_functionField_isFractionRing L
      have hinner : C.functionField_tensor_locBaseChange L =
          (IsLocalization.algEquiv (nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing))
            (L ⊗[F] C.toAffine.FunctionField)
            (FractionRing (L ⊗[F] C.toAffine.CoordinateRing))).restrictScalars L := rfl
      rw [hinner, AlgEquiv.restrictScalars_apply]
      exact (IsLocalization.algEquiv (nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing))
          (L ⊗[F] C.toAffine.FunctionField)
          (FractionRing (L ⊗[F] C.toAffine.CoordinateRing))).commutes (1 ⊗ₜ[F] u)
  have h := RingHom.congr_fun hrh z
  rw [RingHom.comp_apply] at h
  rw [← h]
  rfl

/-- **The base-changed pullback intertwines `f` with the natural inclusion** (Silverman I.2):

  `baseChangePullback f (functionFieldMap z) = functionFieldMap (f z)`.

Immediate from `tensorFunctionFieldEquiv_one_tmul`: `Φ⁻¹(functionFieldMap z) = 1 ⊗ z`,
`(id_L ⊗ f)(1 ⊗ z) = 1 ⊗ f z` (`lTensorMap_tmul`), `Φ(1 ⊗ f z) = functionFieldMap (f z)`. -/
theorem baseChangePullback_functionFieldMap
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField)
    (z : C.toAffine.FunctionField) :
    baseChangePullback C L f (C.functionFieldMap L z) =
      C.functionFieldMap L (f z) := by
  let := C.isDomain_tensorCoordRing L
  rw [baseChangePullback_apply]
  rw [show (tensorFunctionFieldEquiv C L).symm (C.functionFieldMap L z) = 1 ⊗ₜ[F] z from ?_]
  · rw [lTensorMap_tmul, tensorFunctionFieldEquiv_one_tmul]
  · rw [← tensorFunctionFieldEquiv_one_tmul C L z, AlgEquiv.symm_apply_apply]


end Compat

section GenericCoords

variable {K : Type*} [Field K] (W : WeierstrassCurve K)
variable (L : Type*) [Field L] [Algebra K L]

/-- `coordRingMap` sends the `X`-generator class to the `X`-generator class. -/
theorem coordRingMap_X_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) =
      algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X := by
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K L)
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  rw [show ((Polynomial.C Polynomial.X : Polynomial (Polynomial K)).map
        (Polynomial.mapRingHom (algebraMap K L))) =
        Polynomial.C Polynomial.X by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]]
  change WeierstrassCurve.Affine.CoordinateRing.mk (W.baseChange L).toAffine
    (Polynomial.C Polynomial.X) =
    algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X
  rfl

/-- `coordRingMap` sends the `Y`-generator (the `AdjoinRoot` root) to the `Y`-generator. -/
theorem coordRingMap_Y_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
        (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.baseChange L).toAffine.polynomial := by
  rw [← AdjoinRoot.mk_X]
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K L)
    (AdjoinRoot.mk W.toAffine.polynomial Polynomial.X) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]
  rfl

/-- **Base change sends `x_gen^K` to `x_gen^{K̄}`** (Silverman I.2): `functionFieldMap (x_gen W) =
x_gen (W.baseChange L)`. -/
theorem functionFieldMap_x_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (HasseWeil.x_gen W) =
      HasseWeil.x_gen (W.baseChange L) := by
  rw [HasseWeil.x_gen]
  rw [SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_X_gen]
  rfl

/-- **Base change sends `y_gen^K` to `y_gen^{K̄}`** (Silverman I.2): `functionFieldMap (y_gen W) =
y_gen (W.baseChange L)`. -/
theorem functionFieldMap_y_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (HasseWeil.y_gen W) =
      HasseWeil.y_gen (W.baseChange L) := by
  rw [HasseWeil.y_gen]
  rw [SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_Y_gen]
  rfl

end GenericCoords

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic]

/-! ### The algebra `K(E) → K(E_L)` and the square instances for `KaehlerDifferential.map` -/

/-- The `K(E)`-algebra structure on `K(E_L)` via the function-field base-change `K`-algebra hom
`functionField_baseChange` (so `algebraMap K(E) K(E_L) = functionFieldMap`). -/
noncomputable scoped instance algFunctionFieldBaseChange :
    Algebra W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField :=
  ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange L).toAlgebra

omit [DecidableEq K] [W.toAffine.IsElliptic] [DecidableEq L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic] in
/-- `algebraMap K(E) K(E_L) = functionFieldMap` (definitional via `functionField_baseChange`). -/
theorem algebraMap_functionField_baseChange_eq (z : W.toAffine.FunctionField) :
    algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z := rfl

/-- The bottom-left/top tower `K → K(E) → K(E_L)` (the `K`-algebra hom `functionField_baseChange`
factors `K → K(E_L)` through `K → K(E)`). -/
noncomputable scoped instance towerFunctionFieldBaseChange :
    IsScalarTower K W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap K (W.baseChange L).toAffine.FunctionField k =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
        (algebraMap K W.toAffine.FunctionField k)
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F]
    rfl

/-- `SMulCommClass L K(E) K(E_L)`: both act by multiplication in the commutative ring `K(E_L)`. -/
noncomputable scoped instance smulCommFunctionFieldBaseChange :
    SMulCommClass L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField where
  smul_comm l s b := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring

/-! ### The differential transport map `diffMap : Ω[K(E)/K] → Ω[K(E_L)/L]` -/

/-- **The base-change map on Kähler differentials** `Ω[K(E)/K] →ₗ[K(E)] Ω[K(E_L)/L]`, for the
square `K → K(E)`, `L → K(E_L)` with `algebraMap K(E) K(E_L) = functionFieldMap`. -/
noncomputable def omegaDiffMap :
    KaehlerDifferential K W.toAffine.FunctionField →ₗ[W.toAffine.FunctionField]
      KaehlerDifferential L (W.baseChange L).toAffine.FunctionField :=
  KaehlerDifferential.map K L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField

omit [DecidableEq K] [W.toAffine.IsElliptic] [DecidableEq L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic] in
/-- `omegaDiffMap (D_K z) = D_L (functionFieldMap z)` (`KaehlerDifferential.map_D`). -/
theorem omegaDiffMap_D (z : W.toAffine.FunctionField) :
    omegaDiffMap W L (KaehlerDifferential.D K W.toAffine.FunctionField z) =
      KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField
        (algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z) :=
  KaehlerDifferential.map_D K L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z

omit [DecidableEq K] [W.toAffine.IsElliptic] [DecidableEq L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic] in
/-- `omegaDiffMap (s • ω) = s • omegaDiffMap ω` (`K(E)`-linearity, the `K(E)`-action on
`Ω[K(E_L)/L]`
factoring through `functionFieldMap`). -/
theorem omegaDiffMap_smul (s : W.toAffine.FunctionField)
  (ω : KaehlerDifferential K W.toAffine.FunctionField) :
    omegaDiffMap W L (s • ω) = s • omegaDiffMap W L ω :=
  LinearMap.map_smul (omegaDiffMap W L) s ω

/-- **`functionFieldMap` intertwines `α.pullback` with `α_L.pullback`** for a base-changed isogeny,
i.e. the function-field shadow of `α_L = α` over `L` (`baseChangePullback_functionFieldMap`). -/
theorem functionFieldMap_pullback
    (α : Isogeny W.toAffine W.toAffine)
    (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (hpb : α_L.pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback)
    (z : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (α.pullback z) =
      α_L.pullback ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z) := by
  rw [hpb]
  exact (baseChangePullback_functionFieldMap
    (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback z).symm

/-- **Pullback compatibility**: `omegaDiffMap ∘ α.pullbackKaehler = α_L.pullbackKaehler ∘
omegaDiffMap`
for a base-changed isogeny `α_L` whose pullback is `baseChangePullback α.pullback`.  Proved by span
induction over the generators `D_K z`; the generator step is exactly `functionFieldMap_pullback`. -/
theorem omegaDiffMap_pullbackKaehler
    (α : Isogeny W.toAffine W.toAffine)
    (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (hpb : α_L.pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback)
    (ω : KaehlerDifferential K W.toAffine.FunctionField) :
    omegaDiffMap W L (α.pullbackKaehler ω) = α_L.pullbackKaehler (omegaDiffMap W L ω) := by
  have hω : ω ∈ Submodule.span W.toAffine.FunctionField
      (Set.range (KaehlerDifferential.D K W.toAffine.FunctionField)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [Isogeny.pullbackKaehler_D, omegaDiffMap_D, omegaDiffMap_D, Isogeny.pullbackKaehler_D]
    congr 1
    rw [algebraMap_functionField_baseChange_eq, algebraMap_functionField_baseChange_eq]
    exact functionFieldMap_pullback W L α α_L hpb z
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul s x _ hx =>
    rw [Isogeny.pullbackKaehler_smul_KE, omegaDiffMap_smul, hx, omegaDiffMap_smul]
    rw [show (α.pullback s) • α_L.pullbackKaehler (omegaDiffMap W L x) =
        algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField (α.pullback s) •
          α_L.pullbackKaehler (omegaDiffMap W L x) from (algebraMap_smul _ _ _).symm,
      show s • omegaDiffMap W L x =
        algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField s •
          omegaDiffMap W L x from (algebraMap_smul _ _ _).symm]
    rw [Isogeny.pullbackKaehler_smul_KE]
    congr 1
    rw [algebraMap_functionField_baseChange_eq, algebraMap_functionField_baseChange_eq]
    exact functionFieldMap_pullback W L α α_L hpb s

omit [DecidableEq K] [DecidableEq L] [W.toAffine.IsElliptic]
  [Algebra.IsAlgebraic K L] [(W.baseChange L).toAffine.IsElliptic] in
/-- **`functionFieldMap (u_gen) = u_gen` over `L`** (the invariant-differential denominator
`u = 2y + a₁x + a₃` base-changes, since `x_gen`, `y_gen`, `a₁`, `a₃` do). -/
theorem functionFieldMap_u_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (u_gen W) = u_gen (W.baseChange L) := by
  have hx : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (x_gen W) = x_gen
    (W.baseChange L) :=
    functionFieldMap_x_gen W L
  have hy : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (y_gen W) = y_gen
    (W.baseChange L) :=
    functionFieldMap_y_gen W L
  rw [show u_gen W = 2 * y_gen W + algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃ from rfl]
  rw [show u_gen (W.baseChange L) = 2 * y_gen (W.baseChange L) +
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₁ * x_gen
        (W.baseChange L) +
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₃ from rfl]
  rw [map_add, map_add, map_mul, map_mul, map_ofNat, hx, hy,
    SmoothPlaneCurve.functionFieldMap_algebraMap_F, SmoothPlaneCurve.functionFieldMap_algebraMap_F]
  congr 2

omit [DecidableEq K] [DecidableEq L] in
omit [W.toAffine.IsElliptic] [Algebra.IsAlgebraic K L] [(W.baseChange L).toAffine.IsElliptic] in
/-- **The invariant differential transports**: `omegaDiffMap (ω_K) = ω_L`.  Both are
`u⁻¹ • D(x_gen)`, and `functionFieldMap` carries `u_gen ↦ u_gen` (`functionFieldMap_u_gen`) and
`x_gen ↦ x_gen` (`functionFieldMap_x_gen`). -/
theorem omegaDiffMap_invariantDifferential :
    omegaDiffMap W L (invariantDifferential W.toAffine) =
      invariantDifferential (W.baseChange L).toAffine := by
  rw [show invariantDifferential W.toAffine =
      (u_gen W)⁻¹ • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) from rfl]
  rw [omegaDiffMap_smul, omegaDiffMap_D]
  rw [show invariantDifferential (W.baseChange L).toAffine =
      (u_gen (W.baseChange L))⁻¹ •
        KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField (x_gen (W.baseChange L))
      from rfl]
  rw [show (u_gen W)⁻¹ • KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField
        (algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField (x_gen W)) =
      algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField ((u_gen W)⁻¹) •
        KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField
          (algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField (x_gen W))
      from (algebraMap_smul _ _ _).symm]
  rw [algebraMap_functionField_baseChange_eq, algebraMap_functionField_baseChange_eq, map_inv₀,
    functionFieldMap_u_gen]
  congr 2
  rw [show x_gen W = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) from rfl]
  exact functionFieldMap_x_gen W L

/-- **The omega-coefficient base-change transport (Silverman III.5)**: for a base-changed isogeny
`α_L` whose pullback is the concrete `baseChangePullback α.pullback`,

  `omegaPullbackCoeff (E_L) α_L = functionFieldMap (omegaPullbackCoeff E α)`.

The differential analogue of the degree base change `baseChangePullback_finrank_eq`.  Proof:
`a_{α_L} • ω_L = α_L^* ω_L = α_L^* (omegaDiffMap ω_K) = omegaDiffMap (α^* ω_K) =
omegaDiffMap (a_α • ω_K) = a_α • ω_L = functionFieldMap(a_α) • ω_L`, then uniqueness of the
omega coefficient. -/
theorem omegaPullbackCoeff_baseChangePullback
    (α : Isogeny W.toAffine W.toAffine)
    (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (hpb : α_L.pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback) :
    omegaPullbackCoeff (W.baseChange L) α_L =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (omegaPullbackCoeff W α) := by
  apply omegaPullbackCoeff_unique
  rw [← Isogeny.pullbackKaehler_invariantDifferential α_L,
    ← omegaDiffMap_invariantDifferential W L,
    ← omegaDiffMap_pullbackKaehler W L α α_L hpb,
    Isogeny.pullbackKaehler_invariantDifferential α,
    omegaDiffMap_smul, omegaDiffMap_invariantDifferential W L,
    ← algebraMap_functionField_baseChange_eq, algebraMap_smul]



end HasseWeil.OmegaBaseChangeProof

open HasseWeil WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.OmegaIntegralityProof

private theorem translation_derivative_identity {F : Type*} [Field F]
    (a1 a2 a3 a4 a6 x y X Y : F) (hden : x - X ≠ 0)
    (hW : y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6)
    (hP : Y ^ 2 + a1 * X * Y + a3 * Y = X ^ 3 + a2 * X ^ 2 + a4 * X + a6) :
    let l := (y - Y) / (x - X)
    let xt := l ^ 2 + a1 * l - a2 - x - X
    let yt := -l * (xt - x) - y - a1 * xt - a3
    (2 * l + a1) * ((3 * x ^ 2 + 2 * a2 * x + a4 - a1 * y) / (x - X) -
      (y - Y) * (2 * y + a1 * x + a3) / (x - X) ^ 2) - (2 * y + a1 * x + a3) =
      2 * yt + a1 * xt + a3 := by
  dsimp only
  field_simp [hden]
  linear_combination
    -(a1 * (x - X) + 2 * (y - Y)) * hW +
      (a1 * (x - X) + 2 * (y - Y)) * hP

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

private theorem Dω_translateSlope (x y : F) :
    Dω W (translateSlope_xy W x y) =
      (3 * x_gen W ^ 2 + 2 * algebraMap F KE W.a₂ * x_gen W +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * y_gen W) /
          (x_gen W - algebraMap F KE x) -
        (y_gen W - algebraMap F KE y) * u_gen W /
          (x_gen W - algebraMap F KE x) ^ 2 := by
  rw [translateSlope_xy_eq, div_eq_mul_inv, Dω_mul, Dω_inv, Dω_sub, Dω_sub,
    Dω_algebraMap, Dω_algebraMap, sub_zero, sub_zero, Dω_x_gen, Dω_y_gen]
  simp only [div_eq_mul_inv, inv_pow]
  ring

private theorem Dω_translateX (x y : F) (hP : W.toAffine.Equation x y) :
    Dω W (translateX_xy W x y) =
      2 * translateY_xy W x y + algebraMap F KE W.a₁ * translateX_xy W x y +
        algebraMap F KE W.a₃ := by
  have hcurve := generic_equation W
  have hpoint := translate_constant_equation W x y hP
  rw [Affine.equation_iff] at hcurve hpoint
  have hden : x_gen W - algebraMap F KE x ≠ 0 :=
    x_gen_sub_const_ne_zero W x
  have hderiv := translation_derivative_identity
    (algebraMap F KE W.a₁) (algebraMap F KE W.a₂) (algebraMap F KE W.a₃)
    (algebraMap F KE W.a₄) (algebraMap F KE W.a₆)
    (x_gen W) (y_gen W) (algebraMap F KE x) (algebraMap F KE y) hden hcurve hpoint
  have ha₁ : (W_KE W).toAffine.a₁ = algebraMap F KE W.a₁ := rfl
  have ha₂ : (W_KE W).toAffine.a₂ = algebraMap F KE W.a₂ := rfl
  have ha₃ : (W_KE W).toAffine.a₃ = algebraMap F KE W.a₃ := rfl
  rw [translateX_xy, Affine.addX, ha₁, ha₂, Dω_sub, Dω_sub, Dω_sub, Dω_add, Dω_pow,
    Dω_mul, Dω_algebraMap, Dω_algebraMap, Dω_algebraMap, Dω_x_gen]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero]
  rw [Dω_translateSlope, translateY_xy, Affine.addY, Affine.negY, Affine.negAddY,
    Affine.addX, translateSlope_xy_eq]
  have hu : u_gen W = 2 * y_gen W + algebraMap F KE W.a₁ * x_gen W +
      algebraMap F KE W.a₃ := rfl
  simp only [hu, ha₁, ha₂, ha₃]
  dsimp only at hderiv
  simp only [div_eq_mul_inv] at hderiv ⊢
  convert hderiv using 1 <;> ring

noncomputable def translationIsogeny (P : W.toAffine.Point) :
    Isogeny W.toAffine W.toAffine where
  pullback := (translateAlgEquivOfPoint W P).toAlgHom
  toAddMonoidHom := 0

private theorem omega_translationIsogeny (P : W.toAffine.Point) :
    omegaPullbackCoeff W (translationIsogeny W P) = 1 := by
  cases P with
  | zero =>
    apply omegaPullbackCoeff_unique
    rw [omegaPullbackCoeff_spec]
    change (u_gen W)⁻¹ • KaehlerDifferential.D F KE (x_gen W) =
      (1 : KE) • invariantDifferential W.toAffine
    rw [one_smul]
    rfl
  | some x y hns =>
    have hD := Dω_spec W (translateX_xy W x y)
    rw [Dω_translateX W x y hns.left] at hD
    have hx : (translationIsogeny W (.some x y hns)).pullback (x_gen W) =
        translateX_xy W x y := translateAlgEquivOfPoint_apply_x_gen W x y hns
    have hy : (translationIsogeny W (.some x y hns)).pullback (y_gen W) =
        translateY_xy W x y := translateAlgEquivOfPoint_apply_y_gen W x y hns
    have hu : alpha_star_u W (translationIsogeny W (.some x y hns)) =
        2 * translateY_xy W x y + algebraMap F KE W.a₁ * translateX_xy W x y +
          algebraMap F KE W.a₃ := by
      change 2 * (translationIsogeny W (.some x y hns)).pullback (y_gen W) +
        algebraMap F KE W.a₁ * (translationIsogeny W (.some x y hns)).pullback (x_gen W) +
          algebraMap F KE W.a₃ = _
      rw [hx, hy]
    apply omegaPullbackCoeff_unique
    rw [omegaPullbackCoeff_spec]
    change (alpha_star_u W (translationIsogeny W (.some x y hns)))⁻¹ •
      KaehlerDifferential.D F KE ((translationIsogeny W (.some x y hns)).pullback (x_gen W)) = _
    rw [hx, hD, ← hu, smul_smul,
      inv_mul_cancel₀ (alpha_star_u_ne_zero W (translationIsogeny W (.some x y hns))), one_smul]

private theorem omega_comp (α β : Isogeny W.toAffine W.toAffine) :
    omegaPullbackCoeff W (α.comp β) =
      β.pullback (omegaPullbackCoeff W α) * omegaPullbackCoeff W β := by
  apply omegaPullbackCoeff_unique
  rw [← Isogeny.pullbackKaehler_invariantDifferential (α.comp β),
    Isogeny.pullbackKaehler_comp, AddMonoidHom.comp_apply,
    Isogeny.pullbackKaehler_invariantDifferential α,
    Isogeny.pullbackKaehler_smul_KE,
    Isogeny.pullbackKaehler_invariantDifferential β, smul_smul]


private theorem omega_order_at_point_nonneg (α : Isogeny W.toAffine W.toAffine)
    (P : (W_smooth W).SmoothPoint) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (omegaPullbackCoeff W α) := by
  have hnonneg :=
    HasseWeil.OmegaRegularityProof.omegaPullbackCoeff_ordAtInfty_nonneg_proof W
    (α.comp (translationIsogeny W P.toAffinePoint))
  have hcomp : omegaPullbackCoeff W (α.comp (translationIsogeny W P.toAffinePoint)) =
      translateAlgEquivOfPoint W P.toAffinePoint (omegaPullbackCoeff W α) := by
    calc
      _ = (translationIsogeny W P.toAffinePoint).pullback (omegaPullbackCoeff W α) *
          omegaPullbackCoeff W (translationIsogeny W P.toAffinePoint) := omega_comp W _ _
      _ = (translationIsogeny W P.toAffinePoint).pullback (omegaPullbackCoeff W α) * 1 :=
        congrArg (fun c : KE ↦ (translationIsogeny W P.toAffinePoint).pullback
          (omegaPullbackCoeff W α) * c) (omega_translationIsogeny W P.toAffinePoint)
      _ = _ := mul_one _
  have hnonneg' : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
      (translateAlgEquivOfPoint W P.toAffinePoint (omegaPullbackCoeff W α)) :=
    (congrArg (fun f : KE ↦ (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty f) hcomp).mp hnonneg
  have htransport := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W P
    (-P.toAffinePoint) (add_neg_cancel P.toAffinePoint)
    ((translateAlgEquivOfPoint W P.toAffinePoint) (omegaPullbackCoeff W α))
  have hcancel : translateAlgEquivOfPoint W (-P.toAffinePoint)
      (translateAlgEquivOfPoint W P.toAffinePoint (omegaPullbackCoeff W α)) =
        omegaPullbackCoeff W α :=
    (translateAlgEquivOfPoint_add_apply W P.toAffinePoint (-P.toAffinePoint)
      (omegaPullbackCoeff W α)).symm.trans
        ((congrArg (fun Q : W.toAffine.Point ↦ translateAlgEquivOfPoint W Q
          (omegaPullbackCoeff W α))
          (add_neg_cancel (P.toAffinePoint : W.toAffine.Point))).trans
            (translateAlgEquivOfPoint_zero_apply W (omegaPullbackCoeff W α)))
  have horder : (W_smooth W).ord_P P (omegaPullbackCoeff W α) =
      (W_smooth W).ordAtInfty
        (translateAlgEquivOfPoint W P.toAffinePoint (omegaPullbackCoeff W α)) :=
    (congrArg ((W_smooth W).ord_P P) hcancel).symm.trans htransport
  exact (congrArg (fun z : WithTop ℤ ↦ 0 ≤ z) horder).mpr hnonneg'

private theorem omega_constant_of_algClosed [IsAlgClosed F]
    (α : Isogeny W.toAffine W.toAffine) :
    ∃ c : F, omegaPullbackCoeff W α = algebraMap F KE c := by
  by_cases hzero : omegaPullbackCoeff W α = 0
  · exact ⟨0, by simpa using hzero⟩
  have hcoord := noFinitePolesBridge_unconditional W.toAffine (omegaPullbackCoeff W α) hzero
    (omega_order_at_point_nonneg W α)
  exact (W_smooth W).const_of_no_poles_of_coordinateRing _ hcoord
    (HasseWeil.OmegaRegularityProof.omegaPullbackCoeff_ordAtInfty_nonneg_proof W α)


theorem omegaPullbackCoeff_isIntegral_polynomialX_proof
    (α : Isogeny W.toAffine W.toAffine) :
    IsIntegral (Polynomial F) (omegaPullbackCoeff W α) := by
  classical
  let L := AlgebraicClosure F
  let β : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine :=
    { pullback := HasseWeil.OmegaBaseChangeProof.baseChangePullback (W_smooth W) L α.pullback,
      toAddMonoidHom := 0 }
  have hbc := HasseWeil.OmegaBaseChangeProof.omegaPullbackCoeff_baseChangePullback W L α β rfl
  obtain ⟨c, hc⟩ := omega_constant_of_algClosed (W.baseChange L) β
  have hintL : IsIntegral F ((W_smooth W).functionFieldMap L (omegaPullbackCoeff W α)) := by
    have hintC : IsIntegral F (algebraMap L (W.baseChange L).toAffine.FunctionField c) :=
      (Algebra.IsIntegral.isIntegral c).map
        (IsScalarTower.toAlgHom F L (W.baseChange L).toAffine.FunctionField)
    exact (congrArg (fun f : (W.baseChange L).toAffine.FunctionField ↦ IsIntegral F f)
      (hbc.symm.trans hc)).mpr hintC
  have hint : IsIntegral F (omegaPullbackCoeff W α) :=
    (isIntegral_algHom_iff ((W_smooth W).functionField_baseChange L)
      ((W_smooth W).functionField_baseChange L).injective).mp hintL
  exact hint.tower_top

end HasseWeil.OmegaIntegralityProof

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
local notation "KE" => W.toAffine.FunctionField

/-- The differential pullback coefficient has no finite poles, so it is integral over `F[X]`.
Translation transports infinity regularity to every finite point; scalar extension to an
algebraic closure and integral descent cover arbitrary base fields. -/
theorem omegaPullbackCoeff_isIntegral_polynomialX
    (α : Isogeny W.toAffine W.toAffine) :
    IsIntegral (Polynomial F) (omegaPullbackCoeff W α) := by
  exact OmegaIntegralityProof.omegaPullbackCoeff_isIntegral_polynomialX_proof W α

/-- The differential pullback coefficient is regular at infinity. Use the formal chart when
the pulled-back x-coordinate has a pole and a nonsingular affine chart otherwise. -/
theorem omegaPullbackCoeff_ordAtInfty_nonneg
    (α : Isogeny W.toAffine W.toAffine) :
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty
        (omegaPullbackCoeff W α) := by
  exact OmegaRegularityProof.omegaPullbackCoeff_ordAtInfty_nonneg_proof W α

/-- The differential pullback coefficient is constant: integrality excludes finite poles,
and nonnegative infinity order completes the algebraic Liouville argument. -/
theorem omegaPullbackCoeff_mem_F (α : Isogeny W.toAffine W.toAffine) :
    ∃ c : F, omegaPullbackCoeff W α = algebraMap F KE c := by
  have h_int := omegaPullbackCoeff_isIntegral_polynomialX W α
  have h_inf := omegaPullbackCoeff_ordAtInfty_nonneg W α
  have h_const :=
    HasseWeil.Curves.SmoothPlaneCurve.const_of_isIntegral_polynomialX_of_ordAtInfty
      (C := (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F)) h_int h_inf
  obtain ⟨c, hc⟩ := h_const
  exact ⟨c, hc⟩

theorem omegaPullbackCoeff_localExpand_eq_coeff_one
    (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (omegaPullbackCoeff W α) =
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.C (PowerSeries.coeff 1 (formalIsogenySeries W α))) := by
  obtain ⟨c, hc⟩ := omegaPullbackCoeff_mem_F W α
  rw [hc, localExpand_algebraMap W, omegaPullbackCoeff_F_value_eq_coeff_one W α h_α c hc]

/-- The curve-to-formal coefficient bridge for an isogeny whose pulled-back x-coordinate
has a pole at infinity. The x-pole hypothesis excludes translations to finite zeros of the
local parameter, for which positive order of the pulled-back parameter alone is insufficient. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization
    (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    omegaPullbackCoeff W α =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α)) := by
  apply localExpand_injective W
  rw [omegaPullbackCoeff_localExpand_eq_coeff_one W α h_α, localExpand_algebraMap W]

/-- The invariant-differential pullback coefficient equals the linear coefficient of
the formal isogeny series when the pulled-back x-coordinate has a pole at infinity. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading
    (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    omegaPullbackCoeff W α =
      algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α)) :=
  omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization W α h_α

/-- **TOP** (Silverman III.5.3, p. 79): `omegaPullbackCoeff [m] = m` for `m ≠ 0`, wronskian-free,
via the formal group. Chains BRIDGE-001 (localization route) + L-F1; the genuineness input is
discharged from the unconditional pole fact `ordAtInfty_mulByInt_x_neg` (`OrdAtInftyBridge.lean`)
through `orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg`. (`m ≠ 0` is required:
`mulByInt 0` is not an isogeny and its placeholder pullback is not genuine.) -/
theorem omegaPullbackCoeff_mulByInt_via_formalGroup (m : ℤ) (hm : m ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine m) = algebraMap F KE (m : F) := by
  have h_x_neg : (W_smooth W).ordAtInfty
      ((mulByInt W.toAffine m).pullback (x_gen W)) < 0 := by
    have h_pb : (mulByInt W.toAffine m).pullback (x_gen W) = mulByInt_x W m :=
      mulByInt_pullback_x W m hm
    rw [h_pb]
    exact ordAtInfty_mulByInt_x_neg W m hm
  rw [omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization W (mulByInt W.toAffine m) h_x_neg,
    coeff_one_formalIsogenySeries_mulByInt_eq W m hm]

/-- **Pillar B start, wronskian-free** (Silverman III.5.3 at `m = p`, char `p > 0`): `[p]*ω = 0`.
Immediate from the TOP `omegaPullbackCoeff_mulByInt_via_formalGroup` (`a_{[p]} = (p : F)`) +
`CharP.cast_eq_zero`. This is the wronskian-free replacement for `T01`
(`mulByInt_p_omega_pullback_eq_zero`, which currently routes through the EDS wronskian via
`omegaPullbackCoeff_mulByInt`). SORRY-FREE modulo the four kernel leaves. -/
theorem omegaPullbackCoeff_mulByInt_p_eq_zero_via_formalGroup
    (p : ℕ) [CharP F p] (hp : p ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine (p : ℤ)) = 0 := by
  rw [omegaPullbackCoeff_mulByInt_via_formalGroup W (p : ℤ) (by exact_mod_cast hp),
      show ((p : ℤ) : F) = 0 from by rw [Int.cast_natCast]; exact CharP.cast_eq_zero F p,
      map_zero]

/-- **SK-QTH-Dpx0** (DEV-1 step): `D([p]*x_gen) = 0` in char `p`. From `omegaPullbackCoeff_spec`
(`a_{[p]} • ω = ([p]*u)⁻¹ • D([p]*x)`) + `a_{[p]} = 0`, since `([p]*u)⁻¹ ≠ 0`. This feeds the
char-`p` Kähler-kernel route to `Im([p]*) ⊆ K(E)^p` (the q-th-root). -/
theorem D_mulByInt_p_pullback_x_gen_eq_zero [Fintype F] (p : ℕ) [CharP F p] [Fact p.Prime] :
    KaehlerDifferential.D F KE
        ((mulByInt W.toAffine (p : ℤ)).pullback (x_gen W)) = 0 := by
  have hspec := omegaPullbackCoeff_spec W (mulByInt W.toAffine (p : ℤ))
  -- `a_{[p]} = 0` (char p) via the axiom-clean Route B chain (wronskian-free, formal-group-free).
  rw [omegaPullbackCoeff_mulByInt_p_eq_zero_routeB W p (Fact.out (p := p.Prime)).pos.ne',
    zero_smul] at hspec
  have hu : alpha_star_u W (mulByInt W.toAffine (p : ℤ)) ≠ 0 := by
    rw [alpha_star_u_eq]
    intro h
    exact u_gen_ne_zero W
      ((mulByInt W.toAffine (p : ℤ)).pullback_injective (by rw [h, map_zero]))
  exact (smul_eq_zero.mp hspec.symm).resolve_left (inv_ne_zero hu)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `D(gᵖ) = 0` in char `p` (`Derivation.leibniz_pow` + `p • · = 0`). -/
theorem kaehlerD_pth_power_eq_zero (p : ℕ) [CharP F p] (g : KE) :
    KaehlerDifferential.D F KE (g ^ p) = 0 := by
  have : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  rw [Derivation.leibniz_pow,
    show (p : ℕ) • (g ^ (p - 1) • KaehlerDifferential.D F KE g) =
        ((p : ℕ) : KE) • (g ^ (p - 1) • KaehlerDifferential.D F KE g) from by
      rw [Nat.cast_smul_eq_nsmul], CharP.cast_eq_zero, zero_smul]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `D` is `K(E)ᵖ`-semilinear: `D(gᵖ·h) = gᵖ·D h` (Leibniz + `D(gᵖ)=0`). This makes `ker D`
a `K(E)ᵖ`-submodule, the key to `ker D = K(E)ᵖ`. -/
theorem kaehlerD_pth_power_mul (p : ℕ) [CharP F p] (g h : KE) :
    KaehlerDifferential.D F KE (g ^ p * h) = g ^ p • KaehlerDifferential.D F KE h := by
  rw [Derivation.leibniz, kaehlerD_pth_power_eq_zero, smul_zero, add_zero]

/-- `D ≠ 0`: some element has nonzero differential. From `kaehler_rank_one` (Ω ≠ 0) +
`span_range_derivation` (Ω = span of `range D`). Gives `ker D ⊊ K(E)` for SK-KERD-FIELD-ARG. -/
theorem kaehlerD_ne_zero : ∃ w : KE, KaehlerDifferential.D F KE w ≠ 0 := by
  by_contra h
  push Not at h
  have hbot : (⊤ : Submodule KE (KaehlerDifferential F KE)) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation F KE]
    apply le_antisymm _ bot_le
    rw [Submodule.span_le]
    rintro x ⟨w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_bot]
    exact h w
  have : Subsingleton (KaehlerDifferential F KE) := ⟨fun a b ↦ by
    have ha : a ∈ (⊥ : Submodule KE (KaehlerDifferential F KE)) := hbot ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule KE (KaehlerDifferential F KE)) := hbot ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb; rw [ha, hb]⟩
  exact one_ne_zero
    ((kaehler_rank_one W.toAffine).symm.trans Module.finrank_zero_of_subsingleton)

/-- **SK-FINRANK-P-1**: `x_gen` is not a `p`-th power. Clean: `D(gᵖ)=0`
(`kaehlerD_pth_power_eq_zero`) but `D(x_gen)≠0` (`D_x_ne_zero`). -/
theorem x_gen_not_pth_power (p : ℕ) [CharP F p] :
    ¬ ∃ w : KE, w ^ p = x_gen W := by
  rintro ⟨w, hw⟩
  have hzero := kaehlerD_pth_power_eq_zero W p w
  rw [hw] at hzero
  exact D_x_ne_zero W.toAffine hzero

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `K(E) / K(E)ᵖ` is purely inseparable: every `x` has `xᵖ = frobenius x ∈ K(E)ᵖ`. Foundation
for SK-KERD-FINRANK-P. -/
theorem isPurelyInseparable_frobeniusRange_p (p : ℕ) [Fact p.Prime] [CharP F p] :
    haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
    IsPurelyInseparable ↥((frobenius KE p).fieldRange) KE := by
  have : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  exact ⟨1, by rw [pow_one]; exact ⟨⟨x ^ p, x, rfl⟩, rfl⟩⟩

/-- **SK-FINRANK-P-3 (degree piece)**: `minpoly K(E)ᵖ x_gen` has degree `p`. From
`IsPurelyInseparable.minpoly_eq_X_pow_sub_C` (`= X^(pⁿ)−C y`, natDegree `pⁿ`): `n≥1` since
`x_gen∉K(E)ᵖ`; `n≤1` since `x_genᵖ∈K(E)ᵖ` (so `minpoly ∣ Xᵖ−x_genᵖ`); `p` prime ⟹ `n=1`. -/
theorem minpoly_x_gen_frobeniusRange_natDegree (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectField F] :
    haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
    (minpoly ↥((frobenius KE p).fieldRange) (x_gen W)).natDegree = p := by
  have : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  have hpi := isPurelyInseparable_frobeniusRange_p W p
  have : ExpChar KE p := ExpChar.prime (Fact.out : p.Prime)
  have hcKp : CharP ↥((frobenius KE p).fieldRange) p :=
    (RingHom.charP_iff (algebraMap ↥((frobenius KE p).fieldRange) KE)
      (algebraMap ↥((frobenius KE p).fieldRange) KE).injective p).mpr ‹CharP KE p›
  have : ExpChar ↥((frobenius KE p).fieldRange) p := ExpChar.prime (Fact.out : p.Prime)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨n, y, hmin⟩ :=
    IsPurelyInseparable.minpoly_eq_X_pow_sub_C (F := ↥((frobenius KE p).fieldRange)) (E := KE)
      p (x_gen W)
  have hdeg : (minpoly ↥((frobenius KE p).fieldRange) (x_gen W)).natDegree = p ^ n := by
    rw [hmin, Polynomial.natDegree_X_pow_sub_C]
  -- The element `x_gen ^ p ∈ K(E)ᵖ` (it is `frobenius x_gen`).
  set c : ↥((frobenius KE p).fieldRange) := ⟨x_gen W ^ p, x_gen W, rfl⟩ with hc
  -- x_gen is a root of `X ^ p - C c` over K(E)ᵖ.
  have hroot : Polynomial.aeval (x_gen W)
      (Polynomial.X ^ p - Polynomial.C c) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    show x_gen W ^ p - (c : KE) = 0
    rw [hc]; exact sub_self _
  have hdvd := minpoly.dvd ↥((frobenius KE p).fieldRange) (x_gen W) hroot
  have hpoly_ne : (Polynomial.X ^ p - Polynomial.C c) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by omega) c
  -- Upper bound: `p ^ n ≤ p`.
  have hub : p ^ n ≤ p := by
    rw [← hdeg]
    refine le_trans (Polynomial.natDegree_le_of_dvd hdvd hpoly_ne) ?_
    rw [Polynomial.natDegree_X_pow_sub_C]
  -- Lower bound: `n ≠ 0` (else `x_gen ∈ K(E)ᵖ`, contradicting `x_gen_not_pth_power`).
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply x_gen_not_pth_power W p
    have hax : (minpoly ↥((frobenius KE p).fieldRange) (x_gen W)).aeval (x_gen W) = 0 :=
      minpoly.aeval _ _
    rw [hmin] at hax
    simp only [pow_zero, pow_one, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      sub_eq_zero] at hax
    obtain ⟨w, hw⟩ := y.2
    rw [frobenius_def] at hw
    exact ⟨w, by rw [hw]; exact hax.symm⟩
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right (le_of_lt hp1) h
    nlinarith [this, hub]
  rw [hdeg, show n = 1 by omega, pow_one]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **SK-FINRANK-P-2 separable input**: `KE / K(E)ᵖ(x_gen)` is separable. From `KE / K(x)` separable
(`K(x) = FractionRing (Polynomial F)`, via `functionField_isSeparable` passed in as `hsep0`) by
tower-top, since `K(x) ⊆ L`. The FractionRing `Algebra`/`IsSeparable` instances are passed
*explicitly*
(`halg`, `hsep0`) because they cannot be synthesised under the `respectTransparency` option this
lemma needs for the nested `Algebra ↥L KE` instance. -/
theorem isSeparable_KE_over_frobeniusRange_adjoin_x_gen (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectField F]
    (halg : haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
      Algebra (FractionRing (Polynomial F)) KE)
    (hsep0 : haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
      @Algebra.IsSeparable (FractionRing (Polynomial F)) KE _ _ halg)
    (htower : haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
      letI : Algebra (FractionRing (Polynomial F)) KE := halg
      IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) KE) :
    haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
    Algebra.IsSeparable
      ↥(IntermediateField.adjoin ↥((frobenius KE p).fieldRange) {x_gen W}) KE := by
  let : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  let : Algebra (FractionRing (Polynomial F)) KE := halg
  have : @Algebra.IsSeparable (FractionRing (Polynomial F)) KE _ _ halg := hsep0
  have : IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) KE := htower
  set L := IntermediateField.adjoin ↥((frobenius KE p).fieldRange) {x_gen W} with hLdef
  -- `himg`: `algebraMap (FractionRing _) KE` lands in `L` (image is `K(x_gen) ⊆ L`).
  have hx : x_gen W ∈ L := by
    rw [hLdef]; exact IntermediateField.subset_adjoin _ _ rfl
  have hXgen : algebraMap (Polynomial F) KE Polynomial.X = x_gen W :=
    IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing
      W.toAffine.FunctionField Polynomial.X
  have hF : ∀ a : F, algebraMap F KE a ∈ L := by
    intro a
    obtain ⟨b, hb⟩ := surjective_frobenius F p a
    rw [frobenius_def] at hb
    exact L.algebraMap_mem ⟨algebraMap F KE a, algebraMap F KE b, by
      rw [frobenius_def, ← map_pow, hb]⟩
  have hpoly : ∀ p : Polynomial F, algebraMap (Polynomial F) KE p ∈ L := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply F (Polynomial F) KE a]
        exact hF a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a _ =>
        rw [map_mul, map_pow, hXgen]
        refine mul_mem ?_ (pow_mem hx _)
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply F (Polynomial F) KE a]
        exact hF a
  have himg : ∀ z : FractionRing (Polynomial F),
      algebraMap (FractionRing (Polynomial F)) KE z ∈ L := by
    intro z
    obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial F) z
    rw [map_div₀, ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE,
      ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE]
    exact div_mem (hpoly r) (hpoly s)
  let : Algebra (FractionRing (Polynomial F)) ↥L :=
    ((algebraMap (FractionRing (Polynomial F)) KE).codRestrict
      L.toSubalgebra.toSubsemiring himg).toAlgebra
  have : IsScalarTower (FractionRing (Polynomial F)) ↥L KE :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact Algebra.isSeparable_tower_top_of_isSeparable (FractionRing (Polynomial F)) ↥L KE

/-- **SK-KERD-FINRANK-P** (char-`p` imperfection degree of the elliptic function field = `p`).
`[K(E) : K(E)ᵖ] = p`, where `K(E)ᵖ = (frobenius KE p).fieldRange`. Route: `K(E) = K(E)ᵖ(x_gen)`
(via `surjective_algebraMap_of_isSeparable`: `KE/K(E)ᵖ(x_gen)` purely-insep ∧ separable), then
`IntermediateField.adjoin.finrank` + `minpoly_x_gen_frobeniusRange_natDegree` (= p) + `finrank_top`.
-/
theorem finrank_KE_over_frobeniusRange_p (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectField F] :
    letI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
    Module.finrank ↥((frobenius KE p).fieldRange) KE = p := by
  let : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  have hpi := isPurelyInseparable_frobeniusRange_p W p
  have hint : IsIntegral ↥((frobenius KE p).fieldRange) (x_gen W) :=
    hpi.isIntegral.isIntegral (x_gen W)
  set L := IntermediateField.adjoin ↥((frobenius KE p).fieldRange) {x_gen W} with hLdef
  have hLpi : IsPurelyInseparable ↥L KE := by
    rw [isPurelyInseparable_iff_pow_mem _ p]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact ⟨⟨x ^ p, IntermediateField.algebraMap_mem _
      (⟨x ^ p, x, rfl⟩ : ↥((frobenius KE p).fieldRange))⟩, rfl⟩
  -- [SK-FINRANK-P-2 separable input] `KE/L` separable; from the helper lemma above, with the
  -- FractionRing `Algebra`/`IsSeparable` instances passed as terms (synthesised in their own
  -- context).
  have hLsep : Algebra.IsSeparable ↥L KE :=
    isSeparable_KE_over_frobeniusRange_adjoin_x_gen W p
      (functionField_algebra_fractionRing W.toAffine) (functionField_isSeparable W.toAffine)
      (functionField_isScalarTower W.toAffine)
  have hLtop : L = ⊤ := by
    refine eq_top_iff.mpr (fun x _ ↦ ?_)
    obtain ⟨l, hl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable ↥L KE x
    rw [← hl]; exact l.2
  have hfin : Module.finrank ↥((frobenius KE p).fieldRange) ↥L = p := by
    rw [hLdef, IntermediateField.adjoin.finrank hint, minpoly_x_gen_frobeniusRange_natDegree W p]
  have htop : Module.finrank ↥((frobenius KE p).fieldRange) KE =
      Module.finrank ↥((frobenius KE p).fieldRange)
        ↥(⊤ : IntermediateField ↥((frobenius KE p).fieldRange) KE) :=
    (LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv).symm
  rw [htop, ← hLtop]
  exact hfin

theorem kaehlerD_eq_zero_iff_mem_pth_powers (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectField F]
    (w : KE) :
    KaehlerDifferential.D F KE w = 0 ↔ ∃ g : KE, g ^ p = w := by
  have : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  refine ⟨?_, ?_⟩
  · -- ⟹ : `ker D` is an IntermediateField `K(E)ᵖ ⊆ ker D ⊊ K(E)`;
    -- `[K(E):K(E)ᵖ]=p` prime ⟹ `ker D = ⊥`.
    intro hw
    have hfin_p : Module.finrank ↥((frobenius KE p).fieldRange) KE = p :=
      finrank_KE_over_frobeniusRange_p W p
    let M : IntermediateField ↥((frobenius KE p).fieldRange) KE :=
      { carrier := {v | KaehlerDifferential.D F KE v = 0}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_ofPred_eq] at *
          rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
        one_mem' := by
          simp only [Set.mem_ofPred_eq]; exact Derivation.map_one_eq_zero _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_ofPred_eq] at *; rw [map_add, ha, hb, add_zero]
        zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_ofPred_eq] at *; rw [Derivation.leibniz_inv, ha, smul_zero]
        algebraMap_mem' := fun c ↦ by
          obtain ⟨g, hg⟩ := c.2
          have hval : (c : KE) = g ^ p := hg.symm
          show KaehlerDifferential.D F KE (algebraMap _ KE c) = 0
          rw [show (algebraMap (↥((frobenius KE p).fieldRange)) KE c) = (c : KE) from rfl, hval]
          exact kaehlerD_pth_power_eq_zero W p g }
    have hwM : w ∈ M := hw
    have hMne : M ≠ ⊤ := by
      obtain ⟨v, hv⟩ := kaehlerD_ne_zero W
      intro hMtop
      have hvM : v ∈ M := by rw [hMtop]; exact IntermediateField.mem_top
      exact hv hvM
    have hMbot : M = ⊥ := by
      have : FiniteDimensional ↥((frobenius KE p).fieldRange) KE :=
        FiniteDimensional.of_finrank_eq_succ (n := p - 1)
          (by have := (Fact.out : p.Prime).two_le; rw [hfin_p]; omega)
      have htower := Module.finrank_mul_finrank ↥((frobenius KE p).fieldRange) ↥M KE
      rw [hfin_p] at htower
      have hdvd : Module.finrank ↥((frobenius KE p).fieldRange) ↥M ∣ p := ⟨_, htower.symm⟩
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
      · exact IntermediateField.finrank_eq_one_iff.mp h1
      · exfalso
        apply hMne
        have heq : Module.finrank ↥((frobenius KE p).fieldRange) ↥M.toSubmodule
            = Module.finrank ↥((frobenius KE p).fieldRange) KE := by
          rw [hfin_p]; exact hp
        have htop_sub : M.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq heq
        refine eq_top_iff.mpr (fun x _ ↦ ?_)
        show x ∈ M.toSubmodule
        rw [htop_sub]; exact Submodule.mem_top
    rw [hMbot] at hwM
    rw [IntermediateField.mem_bot] at hwM
    obtain ⟨c, hc⟩ := hwM
    obtain ⟨g, hg⟩ := c.2
    exact ⟨g, by rw [← frobenius_def, hg]; exact hc⟩
  · rintro ⟨g, rfl⟩
    exact kaehlerD_pth_power_eq_zero W p g

/-- **SK-QTH (p-instance)**: `[p]*x_gen` is a `p`-th power. Concrete reduction: from the proven
`D([p]*x_gen) = 0` (`D_mulByInt_p_pullback_x_gen_eq_zero`) via the char-`p` Kähler kernel. -/
theorem mulByInt_p_pullback_x_gen_mem_pth_powers [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectField F] :
    ∃ g : KE, g ^ p = (mulByInt W.toAffine (p : ℤ)).pullback (x_gen W) :=
  (kaehlerD_eq_zero_iff_mem_pth_powers W p _).mp (D_mulByInt_p_pullback_x_gen_eq_zero W p)

/-! ### Per-α PASS leaves for `omegaPullbackCoeff ∈ (algebraMap F KE).range`

The `.range` form (image-of-algebraMap) is an alternative phrasing of `mem_F`
(formerly consumed through the deleted `FormalGroupBridge.lean` witness wrappers).
Trivial axiom-clean wrappers over the per-α PASS leaves above. -/

/-- **PASS leaf — `omegaPullbackCoeff (Isogeny.id) ∈ algebraMap.range`**. -/
theorem omegaPullbackCoeff_id_isConstant :
    omegaPullbackCoeff W (Isogeny.id W.toAffine) ∈ (algebraMap F KE).range :=
  ⟨1, by rw [omegaPullbackCoeff_id, map_one]⟩

/-- **PASS leaf — `omegaPullbackCoeff (frobeniusIsog) ∈ algebraMap.range`**. -/
theorem omegaPullbackCoeff_frobenius_isConstant [Fintype F] :
    omegaPullbackCoeff W (frobeniusIsog W) ∈ (algebraMap F KE).range :=
  ⟨0, by rw [omegaPullbackCoeff_frobenius, map_zero]⟩

/-- **PASS leaf — `omegaPullbackCoeff (negFrobeniusIsog) ∈ algebraMap.range`**. -/
theorem omegaPullbackCoeff_negFrobeniusIsog_isConstant [Fintype F] :
    omegaPullbackCoeff W (negFrobeniusIsog W) ∈ (algebraMap F KE).range :=
  ⟨0, by rw [omegaPullbackCoeff_negFrobeniusIsog, map_zero]⟩

/-- **PASS leaf — `omegaPullbackCoeff (isogOneSub_negFrobenius) ∈ algebraMap.range`**
for the KEY Hasse-bound isogeny. Requires `[Fact p.Prime] [CharP F p]` inherited
from `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_isConstant
    [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hq : 2 ≤ Fintype.card F) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ∈ (algebraMap F KE).range :=
  ⟨1, by rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq, map_one]⟩

end HasseWeil
