import Carlet.K4ASWeierstrassExceptionalCountProbe
import Carlet.K4ASWeierstrassReverseNumeratorProbe

namespace Carlet

variable {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod 2) K]

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

noncomputable def k4ASWGenericPairs (A B : K) :=
  {p : k4ASWeierstrassPairs A B //
    p.val.1+k4ASC A B ≠ 0 ∧ p.val.2+A+k4ASC A B ≠ 0}

noncomputable instance k4ASWGenericPairsFintype (A B : K) :
    Fintype (k4ASWGenericPairs A B) := by
  classical
  unfold k4ASWGenericPairs
  exact Fintype.ofFinite _

noncomputable def k4ASWSourcePairs (A B : K) :=
  {xd : K × K // xd.1 ≠ 0 ∧
    k4ASD xd.1*(xd.2^2+xd.2)=(A+B)*xd.1^2+A*xd.1}

noncomputable instance k4ASWSourcePairsFintype (A B : K) :
    Fintype (k4ASWSourcePairs A B) := by
  classical
  unfold k4ASWSourcePairs
  exact Fintype.ofFinite _

theorem k4ASWGenericSourceWitness
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (p : k4ASWGenericPairs A B) :
    ∃ s : k4ASWSourcePairs A B,
      k4ASWeierstrassX A s.val.1 s.val.2=p.val.val.1 ∧
      k4ASWeierstrassY A B s.val.1 s.val.2=p.val.val.2 := by
  have hW : k4ASReverseWeierstrassRhs A B p.val.val.1 p.val.val.2 := by
    simpa [k4ASReverseWeierstrassRhs,k4ASC,k4ASWeierstrassPairs] using
      p.val.property
  obtain ⟨x,δ,hx,hcurve,hX,hY⟩ :=
    k4ASWeierstrass_generic_point_has_source n hn hfinrank
      A B p.val.val.1 p.val.val.2 hW p.property.1 p.property.2
  exact ⟨⟨(x,δ),hx,hcurve⟩,hX,hY⟩

noncomputable def k4ASWGenericToSource
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (p : k4ASWGenericPairs A B) :
    k4ASWSourcePairs A B :=
  Classical.choose (k4ASWGenericSourceWitness n hn hfinrank A B p)

theorem k4ASWGenericToSource_spec
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) (p : k4ASWGenericPairs A B) :
    k4ASWeierstrassX A (k4ASWGenericToSource n hn hfinrank A B p).val.1
      (k4ASWGenericToSource n hn hfinrank A B p).val.2=p.val.val.1 ∧
    k4ASWeierstrassY A B (k4ASWGenericToSource n hn hfinrank A B p).val.1
      (k4ASWGenericToSource n hn hfinrank A B p).val.2=p.val.val.2 := by
  exact Classical.choose_spec (k4ASWGenericSourceWitness n hn hfinrank A B p)

theorem k4ASWGenericToSource_injective
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) :
    Function.Injective (k4ASWGenericToSource n hn hfinrank A B) := by
  intro p q hpq
  have hsource :
      (k4ASWGenericToSource n hn hfinrank A B p).val =
      (k4ASWGenericToSource n hn hfinrank A B q).val :=
    congrArg Subtype.val hpq
  have hx := congrArg Prod.fst hsource
  have hδ := congrArg Prod.snd hsource
  have hp := k4ASWGenericToSource_spec n hn hfinrank A B p
  have hq := k4ASWGenericToSource_spec n hn hfinrank A B q
  have hX : p.val.val.1=q.val.val.1 := by
    calc
      p.val.val.1 = k4ASWeierstrassX A
          (k4ASWGenericToSource n hn hfinrank A B p).val.1
          (k4ASWGenericToSource n hn hfinrank A B p).val.2 := hp.1.symm
      _ = k4ASWeierstrassX A
          (k4ASWGenericToSource n hn hfinrank A B q).val.1
          (k4ASWGenericToSource n hn hfinrank A B q).val.2 := by rw [hx,hδ]
      _ = q.val.val.1 := hq.1
  have hY : p.val.val.2=q.val.val.2 := by
    calc
      p.val.val.2 = k4ASWeierstrassY A B
          (k4ASWGenericToSource n hn hfinrank A B p).val.1
          (k4ASWGenericToSource n hn hfinrank A B p).val.2 := hp.2.symm
      _ = k4ASWeierstrassY A B
          (k4ASWGenericToSource n hn hfinrank A B q).val.1
          (k4ASWGenericToSource n hn hfinrank A B q).val.2 := by rw [hx,hδ]
      _ = q.val.val.2 := hq.2
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hX hY

theorem k4ASWGenericPairs_card_le_source
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B : K) :
    Fintype.card (k4ASWGenericPairs A B) ≤ Fintype.card (k4ASWSourcePairs A B) := by
  exact Fintype.card_le_of_injective
    (k4ASWGenericToSource n hn hfinrank A B)
    (k4ASWGenericToSource_injective n hn hfinrank A B)

#print axioms k4ASWGenericToSource_injective
#print axioms k4ASWGenericPairs_card_le_source

end Carlet
