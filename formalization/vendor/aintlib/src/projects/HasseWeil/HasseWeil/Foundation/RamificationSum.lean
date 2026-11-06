import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Ramification sums over the Dedekind-domain prime finset

These lemmas express the modern ramification and inertia identity using the
finite set of prime factors and the fraction-field ranks used in HasseWeil.
-/

namespace HasseWeil

/-- The fundamental identity in the finite-set notation for Dedekind domains. -/
theorem sum_ramification_inertia_finrank
    {R S : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
      Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P = Module.finrank R S := by
  classical
  let : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver (S := S) p).fintype
  rw [Finset.sum_subtype (IsDedekindDomain.primesOverFinset p S)
    (fun P ↦ IsDedekindDomain.mem_primesOverFinset_iff hp0 S (P := P))]
  calc
    (∑ P : p.primesOver S, Ideal.ramificationIdx' p P.1 * Ideal.inertiaDeg' p P.1) =
        ∑ P : p.primesOver S, P.1.ramificationIdx R * P.1.inertiaDeg R := by
      apply Finset.sum_congr rfl
      intro P _
      have : P.1.IsMaximal := P.2.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 P.2)
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p P.1 hp0,
        Ideal.inertiaDeg'_eq_inertiaDeg p P.1]
    _ = Module.finrank R S := Ideal.sum_ramification_inertia_eq_finrank p S

/-- The same identity with the extension degree measured in fraction fields. -/
theorem sum_ramification_inertia_finset
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S K L : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
      Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P = Module.finrank K L := by
  have : FaithfulSMul R S := FaithfulSMul.of_field_isFractionRing R S K L
  exact (sum_ramification_inertia_finrank (S := S) hp0).trans
    (IsFractionRing.finrank_eq R K S L).symm

end HasseWeil
