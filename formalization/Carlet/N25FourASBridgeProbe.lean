import Carlet.N25FourASCertificateProbe
import Carlet.N25InverseAdjoinHelperProbe
import Carlet.N25FieldBridgeProbe
import Carlet.N11K5SubfieldProbe
import Carlet.K4ParametricExtensionProbe
import Carlet.FieldTransport
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
local instance : Fact (Irreducible f25) := ⟨f25_irreducible⟩
local instance : CharP (AdjoinRoot f25) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f25)).injective 2

namespace Carlet
abbrev N25FourField := AdjoinRoot f25
def n25FourRootT : N25FourField := AdjoinRoot.mk f25 n25FourT
def n25FourRootU : N25FourField := AdjoinRoot.mk f25 n25FourU
def n25FourRootD : N25FourField := AdjoinRoot.mk f25 n25FourD
def n25FourRootZ : N25FourField := AdjoinRoot.mk f25 n25FourZ
def n25FourRootS : N25FourField := AdjoinRoot.mk f25 n25FourS
def n25FourRootV : N25FourField := AdjoinRoot.mk f25 n25FourV

private theorem n25Four_eq_of_poly_add {a b q : P17} (h : a + b = f25 * q) :
    AdjoinRoot.mk f25 a = AdjoinRoot.mk f25 b := by
  have hz : AdjoinRoot.mk f25 (a + b) = 0 := AdjoinRoot.mk_eq_zero.mpr ⟨q, h⟩
  have hsum : AdjoinRoot.mk f25 a + AdjoinRoot.mk f25 b = 0 := by
    simpa only [map_add] using hz
  exact CharTwo.add_eq_zero.mp hsum

theorem n25FourU_eq : n25FourRootU = n25FourRootT ^ 2 + n25FourRootT := by
  have h := n25Four_eq_of_poly_add n25FourPolyUeq
  simpa only [n25FourRootT, n25FourRootU, map_add, map_pow] using h.symm

theorem n25FourU_ne_zero : n25FourRootU ≠ 0 := by
  have h := n25K5InvAdjoin_of_poly n25FourPolyUinv
  intro hz
  change AdjoinRoot.mk f25 n25FourU = 0 at hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem n25FourU_add_one_ne_zero : n25FourRootU + 1 ≠ 0 := by
  have h := n25K5InvAdjoin_of_poly n25FourPolyU1inv
  have h' : (n25FourRootU + 1) * AdjoinRoot.mk f25 n25FourIU1 = 1 := by
    simpa only [n25FourRootU, map_add, map_one] using h
  intro hz
  rw [hz, zero_mul] at h'
  exact zero_ne_one h'

theorem n25FourD_eq : n25FourRootU ^ 3 + n25FourRootU + 1 = n25FourRootD := by
  have h := n25Four_eq_of_poly_add n25FourPolyDeq
  simpa only [n25FourRootU, n25FourRootD, map_add, map_pow, map_one] using h

theorem n25FourZ_eq : n25FourRootZ ^ 2 + n25FourRootZ =
    1 / (n25FourRootU ^ 3 + n25FourRootU + 1) := by
  have h := n25K5InvAdjoin_of_poly n25FourPolyZeq
  have h' : n25FourRootD * (n25FourRootZ ^ 2 + n25FourRootZ) = 1 := by
    simpa only [n25FourRootD, n25FourRootZ, map_add, map_pow] using h
  have hd : n25FourRootD ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h'
    exact zero_ne_one h'
  rw [n25FourD_eq]
  apply (eq_div_iff hd).2
  simpa [mul_comm] using h'

theorem n25FourD_ne_zero : n25FourRootU ^ 3 + n25FourRootU + 1 ≠ 0 := by
  intro hz
  have heq := n25FourZ_eq
  rw [hz, div_zero] at heq
  have h := n25K5InvAdjoin_of_poly n25FourPolyZeq
  have hz' : n25FourRootD = 0 := n25FourD_eq ▸ hz
  change (AdjoinRoot.mk f25 n25FourD) * _ = 1 at h
  rw [show AdjoinRoot.mk f25 n25FourD = 0 from hz', zero_mul] at h
  exact zero_ne_one h

theorem n25FourS_eq : n25FourRootS ^ 2 + n25FourRootS =
    n25FourRootU * (n25FourRootU + 1) * n25FourRootZ := by
  have h := n25Four_eq_of_poly_add n25FourPolySeq
  simpa only [n25FourRootS, n25FourRootU, n25FourRootZ, map_add, map_mul, map_pow, map_one] using h

theorem n25FourV_eq : n25FourRootV ^ 2 + n25FourRootV =
    n25FourRootU * n25FourRootS := by
  have h := n25Four_eq_of_poly_add n25FourPolyVeq
  simpa only [n25FourRootV, n25FourRootU, n25FourRootS, map_add, map_mul, map_pow] using h

theorem hasZeroSumSubspace_n25_four_as : HasZeroSumSubspace N25FourField 4 := by
  classical
  exact hasZeroSumSubspace_four_of_k4_as_parameters
    n25FourRootT n25FourRootU n25FourRootZ n25FourRootS n25FourRootV
    n25FourU_eq n25FourU_ne_zero n25FourU_add_one_ne_zero n25FourD_ne_zero
    n25FourZ_eq n25FourS_eq n25FourV_eq

theorem hasZeroSumSubspace_four_of_25_dvd_card {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hdiv : 25 ∣ n) :
    HasZeroSumSubspace K 4 := by
  classical
  let L := AdjoinRoot f25
  have hr : Module.finrank (ZMod 2) L = 25 := by
    have hc : Fintype.card L = 2 ^ 25 := by simpa [L] using adjoinRoot25_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hc
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hc
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, finrank_eq_of_card n hcard] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 4 hasZeroSumSubspace_n25_four_as

#print axioms hasZeroSumSubspace_n25_four_as
#print axioms hasZeroSumSubspace_four_of_25_dvd_card
end Carlet
