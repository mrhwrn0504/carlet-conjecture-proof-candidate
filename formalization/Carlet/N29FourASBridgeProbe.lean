import Carlet.N29FourASCertificateProbe
import Carlet.N29InverseAdjoinHelperProbe
import Carlet.N29FieldBridgeProbe
import Carlet.N11K5SubfieldProbe
import Carlet.K4ParametricExtensionProbe
import Carlet.FieldTransport
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
local instance : Fact (Irreducible f29) := ⟨f29_irreducible⟩
local instance : CharP (AdjoinRoot f29) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f29)).injective 2

namespace Carlet
abbrev N29FourField := AdjoinRoot f29
def n29FourRootT : N29FourField := AdjoinRoot.mk f29 n29FourT
def n29FourRootU : N29FourField := AdjoinRoot.mk f29 n29FourU
def n29FourRootD : N29FourField := AdjoinRoot.mk f29 n29FourD
def n29FourRootZ : N29FourField := AdjoinRoot.mk f29 n29FourZ
def n29FourRootS : N29FourField := AdjoinRoot.mk f29 n29FourS
def n29FourRootV : N29FourField := AdjoinRoot.mk f29 n29FourV

private theorem n29Four_eq_of_poly_add {a b q : P17} (h : a + b = f29 * q) :
    AdjoinRoot.mk f29 a = AdjoinRoot.mk f29 b := by
  have hz : AdjoinRoot.mk f29 (a + b) = 0 := AdjoinRoot.mk_eq_zero.mpr ⟨q, h⟩
  have hsum : AdjoinRoot.mk f29 a + AdjoinRoot.mk f29 b = 0 := by
    simpa only [map_add] using hz
  exact CharTwo.add_eq_zero.mp hsum

theorem n29FourU_eq : n29FourRootU = n29FourRootT ^ 2 + n29FourRootT := by
  have h := n29Four_eq_of_poly_add n29FourPolyUeq
  simpa only [n29FourRootT, n29FourRootU, map_add, map_pow] using h.symm

theorem n29FourU_ne_zero : n29FourRootU ≠ 0 := by
  have h := n29K5InvAdjoin_of_poly n29FourPolyUinv
  intro hz
  change AdjoinRoot.mk f29 n29FourU = 0 at hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem n29FourU_add_one_ne_zero : n29FourRootU + 1 ≠ 0 := by
  have h := n29K5InvAdjoin_of_poly n29FourPolyU1inv
  have h' : (n29FourRootU + 1) * AdjoinRoot.mk f29 n29FourIU1 = 1 := by
    simpa only [n29FourRootU, map_add, map_one] using h
  intro hz
  rw [hz, zero_mul] at h'
  exact zero_ne_one h'

theorem n29FourD_eq : n29FourRootU ^ 3 + n29FourRootU + 1 = n29FourRootD := by
  have h := n29Four_eq_of_poly_add n29FourPolyDeq
  simpa only [n29FourRootU, n29FourRootD, map_add, map_pow, map_one] using h

theorem n29FourZ_eq : n29FourRootZ ^ 2 + n29FourRootZ =
    1 / (n29FourRootU ^ 3 + n29FourRootU + 1) := by
  have h := n29K5InvAdjoin_of_poly n29FourPolyZeq
  have h' : n29FourRootD * (n29FourRootZ ^ 2 + n29FourRootZ) = 1 := by
    simpa only [n29FourRootD, n29FourRootZ, map_add, map_pow] using h
  have hd : n29FourRootD ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h'
    exact zero_ne_one h'
  rw [n29FourD_eq]
  apply (eq_div_iff hd).2
  simpa [mul_comm] using h'

theorem n29FourD_ne_zero : n29FourRootU ^ 3 + n29FourRootU + 1 ≠ 0 := by
  intro hz
  have heq := n29FourZ_eq
  rw [hz, div_zero] at heq
  have h := n29K5InvAdjoin_of_poly n29FourPolyZeq
  have hz' : n29FourRootD = 0 := n29FourD_eq ▸ hz
  change (AdjoinRoot.mk f29 n29FourD) * _ = 1 at h
  rw [show AdjoinRoot.mk f29 n29FourD = 0 from hz', zero_mul] at h
  exact zero_ne_one h

theorem n29FourS_eq : n29FourRootS ^ 2 + n29FourRootS =
    n29FourRootU * (n29FourRootU + 1) * n29FourRootZ := by
  have h := n29Four_eq_of_poly_add n29FourPolySeq
  simpa only [n29FourRootS, n29FourRootU, n29FourRootZ, map_add, map_mul, map_pow, map_one] using h

theorem n29FourV_eq : n29FourRootV ^ 2 + n29FourRootV =
    n29FourRootU * n29FourRootS := by
  have h := n29Four_eq_of_poly_add n29FourPolyVeq
  simpa only [n29FourRootV, n29FourRootU, n29FourRootS, map_add, map_mul, map_pow] using h

theorem hasZeroSumSubspace_n29_four_as : HasZeroSumSubspace N29FourField 4 := by
  classical
  exact hasZeroSumSubspace_four_of_k4_as_parameters
    n29FourRootT n29FourRootU n29FourRootZ n29FourRootS n29FourRootV
    n29FourU_eq n29FourU_ne_zero n29FourU_add_one_ne_zero n29FourD_ne_zero
    n29FourZ_eq n29FourS_eq n29FourV_eq

theorem hasZeroSumSubspace_four_of_29_dvd_card {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hdiv : 29 ∣ n) :
    HasZeroSumSubspace K 4 := by
  classical
  let L := AdjoinRoot f29
  have hr : Module.finrank (ZMod 2) L = 29 := by
    have hc : Fintype.card L = 2 ^ 29 := by simpa [L] using adjoinRoot29_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hc
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hc
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, finrank_eq_of_card n hcard] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 4 hasZeroSumSubspace_n29_four_as

#print axioms hasZeroSumSubspace_n29_four_as
#print axioms hasZeroSumSubspace_four_of_29_dvd_card
end Carlet

