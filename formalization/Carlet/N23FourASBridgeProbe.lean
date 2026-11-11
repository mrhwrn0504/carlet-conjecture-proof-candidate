import Carlet.N23FourASCertificateProbe
import Carlet.N23K5InverseAdjoinProbe
import Carlet.N23FieldBridgeProbe
import Carlet.N11K5SubfieldProbe
import Carlet.K4ParametricExtensionProbe
import Carlet.FieldTransport
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

open Polynomial Carlet
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
local instance : Fact (Irreducible f23) := ⟨f23_irreducible⟩
local instance : CharP (AdjoinRoot f23) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot f23)).injective 2

namespace Carlet
abbrev N23FourField := AdjoinRoot f23
def n23FourRootT : N23FourField := AdjoinRoot.mk f23 n23FourT
def n23FourRootU : N23FourField := AdjoinRoot.mk f23 n23FourU
def n23FourRootD : N23FourField := AdjoinRoot.mk f23 n23FourD
def n23FourRootZ : N23FourField := AdjoinRoot.mk f23 n23FourZ
def n23FourRootS : N23FourField := AdjoinRoot.mk f23 n23FourS
def n23FourRootV : N23FourField := AdjoinRoot.mk f23 n23FourV

private theorem n23Four_eq_of_poly_add {a b q : P17} (h : a + b = f23 * q) :
    AdjoinRoot.mk f23 a = AdjoinRoot.mk f23 b := by
  have hz : AdjoinRoot.mk f23 (a + b) = 0 := AdjoinRoot.mk_eq_zero.mpr ⟨q, h⟩
  have hsum : AdjoinRoot.mk f23 a + AdjoinRoot.mk f23 b = 0 := by
    simpa only [map_add] using hz
  exact CharTwo.add_eq_zero.mp hsum

theorem n23FourU_eq : n23FourRootU = n23FourRootT ^ 2 + n23FourRootT := by
  have h := n23Four_eq_of_poly_add n23FourPolyUeq
  simpa only [n23FourRootT, n23FourRootU, map_add, map_pow] using h.symm

theorem n23FourU_ne_zero : n23FourRootU ≠ 0 := by
  have h := n23K5InvAdjoin_of_poly n23FourPolyUinv
  intro hz
  change AdjoinRoot.mk f23 n23FourU = 0 at hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem n23FourU_add_one_ne_zero : n23FourRootU + 1 ≠ 0 := by
  have h := n23K5InvAdjoin_of_poly n23FourPolyU1inv
  have h' : (n23FourRootU + 1) * AdjoinRoot.mk f23 n23FourIU1 = 1 := by
    simpa only [n23FourRootU, map_add, map_one] using h
  intro hz
  rw [hz, zero_mul] at h'
  exact zero_ne_one h'

theorem n23FourD_eq : n23FourRootU ^ 3 + n23FourRootU + 1 = n23FourRootD := by
  have h := n23Four_eq_of_poly_add n23FourPolyDeq
  simpa only [n23FourRootU, n23FourRootD, map_add, map_pow, map_one] using h

theorem n23FourZ_eq : n23FourRootZ ^ 2 + n23FourRootZ =
    1 / (n23FourRootU ^ 3 + n23FourRootU + 1) := by
  have h := n23K5InvAdjoin_of_poly n23FourPolyZeq
  have h' : n23FourRootD * (n23FourRootZ ^ 2 + n23FourRootZ) = 1 := by
    simpa only [n23FourRootD, n23FourRootZ, map_add, map_pow] using h
  have hd : n23FourRootD ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h'
    exact zero_ne_one h'
  rw [n23FourD_eq]
  apply (eq_div_iff hd).2
  simpa [mul_comm] using h'

theorem n23FourD_ne_zero : n23FourRootU ^ 3 + n23FourRootU + 1 ≠ 0 := by
  intro hz
  have heq := n23FourZ_eq
  rw [hz, div_zero] at heq
  have h := n23K5InvAdjoin_of_poly n23FourPolyZeq
  have hz' : n23FourRootD = 0 := n23FourD_eq ▸ hz
  change (AdjoinRoot.mk f23 n23FourD) * _ = 1 at h
  rw [show AdjoinRoot.mk f23 n23FourD = 0 from hz', zero_mul] at h
  exact zero_ne_one h

theorem n23FourS_eq : n23FourRootS ^ 2 + n23FourRootS =
    n23FourRootU * (n23FourRootU + 1) * n23FourRootZ := by
  have h := n23Four_eq_of_poly_add n23FourPolySeq
  simpa only [n23FourRootS, n23FourRootU, n23FourRootZ, map_add, map_mul, map_pow, map_one] using h

theorem n23FourV_eq : n23FourRootV ^ 2 + n23FourRootV =
    n23FourRootU * n23FourRootS := by
  have h := n23Four_eq_of_poly_add n23FourPolyVeq
  simpa only [n23FourRootV, n23FourRootU, n23FourRootS, map_add, map_mul, map_pow] using h

theorem hasZeroSumSubspace_n23_four_as : HasZeroSumSubspace N23FourField 4 := by
  classical
  exact hasZeroSumSubspace_four_of_k4_as_parameters
    n23FourRootT n23FourRootU n23FourRootZ n23FourRootS n23FourRootV
    n23FourU_eq n23FourU_ne_zero n23FourU_add_one_ne_zero n23FourD_ne_zero
    n23FourZ_eq n23FourS_eq n23FourV_eq

theorem hasZeroSumSubspace_four_of_23_dvd_card {K : Type*}
    [Field K] [Fintype K] [Algebra (ZMod 2) K] (n : ℕ)
    (hcard : Fintype.card K = 2 ^ n) (hdiv : 23 ∣ n) :
    HasZeroSumSubspace K 4 := by
  classical
  let L := AdjoinRoot f23
  have hr : Module.finrank (ZMod 2) L = 23 := by
    have hc : Fintype.card L = 2 ^ 23 := by simpa [L] using adjoinRoot23_card
    rw [← FiniteField.pow_finrank_eq_card 2 L] at hc
    apply Nat.pow_right_injective (by omega : 2 ≤ 2)
    exact hc
  have hd : Module.finrank (ZMod 2) L ∣ Module.finrank (ZMod 2) K := by
    simpa [hr, finrank_eq_of_card n hcard] using hdiv
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := L) (L := K) hd
  exact hasZeroSumSubspace_of_algHom_probe e e.injective 4 hasZeroSumSubspace_n23_four_as

#print axioms hasZeroSumSubspace_n23_four_as
#print axioms hasZeroSumSubspace_four_of_23_dvd_card
end Carlet
