import Carlet.K4ASWeierstrassInverseProbe

namespace Carlet

variable {K : Type*} [Field K] [CharP K 2]

theorem k4ASWeierstrass_equation_implies_numerator_zero
    (A B x δ : K) (hx : x ≠ 0)
    (hEq :
      (k4ASWeierstrassY A B x δ)^2+
        k4ASWeierstrassX A x δ*k4ASWeierstrassY A B x δ+
        B*k4ASWeierstrassY A B x δ =
      (k4ASWeierstrassX A x δ)^3+
        (k4ASC A B+1)*(k4ASWeierstrassX A x δ)^2+
        (A+k4ASC A B)*k4ASWeierstrassX A x δ+
        B*(A+k4ASC A B)+A^2) :
    (k4ASNY A B x δ)^2+(k4ASNX A x δ)*(k4ASNY A B x δ)*x+
      B*(k4ASNY A B x δ)*x^3+(k4ASNX A x δ)^3+
      (k4ASC A B+1)*(k4ASNX A x δ)^2*x^2+
      (A+k4ASC A B)*(k4ASNX A x δ)*x^4+
      (B*(A+k4ASC A B)+A^2)*x^6=0 := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  let L := k4ASNY A B x δ *
    (k4ASNY A B x δ + x*k4ASNX A x δ + x^3*B)
  let W := k4ASNX A x δ *
    (k4ASNX A x δ * (k4ASNX A x δ + x^2*(k4ASC A B+1))+
      x^4*(A+k4ASC A B)) + x^6*B*(A+k4ASC A B)+x^6*A^2
  have hEq' := hEq
  dsimp [k4ASWeierstrassX,k4ASWeierstrassY] at hEq'
  field_simp [k4ASWeierstrassX,k4ASWeierstrassY,
    k4ASNX,k4ASNY,k4ASD,k4ASC,hx] at hEq'
  change L=W at hEq'
  have hsum : L+W=0 := by
    dsimp [L,W]
    linear_combination hEq' + W*h2
  dsimp [L,W,k4ASNX,k4ASNY,k4ASD,k4ASC] at hsum
  dsimp [k4ASNX,k4ASNY,k4ASD,k4ASC]
  linear_combination hsum

def k4ASReverseWeierstrassRhs (A B X Y : K) : Prop :=
  Y^2+X*Y+B*Y = X^3+(k4ASC A B+1)*X^2+
    (A+k4ASC A B)*X+B*(A+k4ASC A B)+A^2

theorem k4ASW_ySpecial_iff_factor (A B X : K) :
    k4ASReverseWeierstrassRhs A B X (A+k4ASC A B) ↔
      (X+k4ASC A B)*(X^2+X+k4ASC A B)=0 := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    dsimp [k4ASReverseWeierstrassRhs,k4ASC] at h ⊢
    linear_combination h+(X*(A^2+B)+X^2+X^2*(A^2+B)+X^3-A*B-A^3)*h2
  · intro h
    dsimp [k4ASReverseWeierstrassRhs,k4ASC]
    dsimp [k4ASC] at h
    linear_combination h-(X*(A^2+B)+X^2+X^2*(A^2+B)+X^3-A*B-A^3)*h2

theorem k4ASW_xSpecial_iff_factor (A B Y : K) :
    k4ASReverseWeierstrassRhs A B (A^2+B) Y ↔
      (Y+A+A^2+B)*(Y+A+B)=0 := by
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    dsimp [k4ASReverseWeierstrassRhs,k4ASC] at h ⊢
    linear_combination h+(Y*A+2*A*B+A^2+3*A^2*B+3*A^2*B^2+
      A^3+A^4+3*A^4*B+A^6+2*B^2+B^3)*h2
  · intro h
    dsimp [k4ASReverseWeierstrassRhs,k4ASC]
    linear_combination h-(Y*A+2*A*B+A^2+3*A^2*B+3*A^2*B^2+
      A^3+A^4+3*A^4*B+A^6+2*B^2+B^3)*h2

theorem k4ASW_ySpecial_points_classified (A B X : K)
    (hW : k4ASReverseWeierstrassRhs A B X (A+k4ASC A B)) :
    X+k4ASC A B=0 ∨ X^2+X+k4ASC A B=0 := by
  rw [k4ASW_ySpecial_iff_factor] at hW
  exact mul_eq_zero.mp hW

theorem k4ASW_xSpecial_points_classified (A B Y : K)
    (hW : k4ASReverseWeierstrassRhs A B (A^2+B) Y) :
    Y+A+A^2+B=0 ∨ Y+A+B=0 := by
  rw [k4ASW_xSpecial_iff_factor] at hW
  exact mul_eq_zero.mp hW

theorem k4ASWeierstrass_inverse_recovers_source
    (A B x δ X Y : K) (hx : x ≠ 0)
    (hR : (k4ASD x)^2*δ+B*x^2*k4ASD x+
      A*x*(x+1)*k4ASD x+A^2*x^2*k4ASD x ≠ 0)
    (hX : X=k4ASWeierstrassX A x δ)
    (hrel : X+k4ASC A B=x*(Y+A+k4ASC A B))
    (hW : k4ASReverseWeierstrassRhs A B X Y) :
    k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x := by
  have hcoord := k4ASWeierstrass_coordinate_relation A B x δ hx
  rw [hX] at hrel
  have hm : x*(Y+A+k4ASC A B) =
      x*(k4ASWeierstrassY A B x δ+A+k4ASC A B) := hrel.symm.trans hcoord
  have heq := mul_left_cancel₀ hx hm
  have hY : Y=k4ASWeierstrassY A B x δ := by
    calc
      Y=(Y+A+k4ASC A B)-(A+k4ASC A B) := by ring
      _=(k4ASWeierstrassY A B x δ+A+k4ASC A B)-
        (A+k4ASC A B) := by rw [heq]
      _=k4ASWeierstrassY A B x δ := by ring
  have hEq :
      (k4ASWeierstrassY A B x δ)^2+
        k4ASWeierstrassX A x δ*k4ASWeierstrassY A B x δ+
        B*k4ASWeierstrassY A B x δ =
      (k4ASWeierstrassX A x δ)^3+
        (k4ASC A B+1)*(k4ASWeierstrassX A x δ)^2+
        (A+k4ASC A B)*k4ASWeierstrassX A x δ+
        B*(A+k4ASC A B)+A^2 := by
    simpa [k4ASReverseWeierstrassRhs,hX,hY] using hW
  have hP := k4ASWeierstrass_equation_implies_numerator_zero A B x δ hx hEq
  have hfac := k4AS_numerator_factorization_six A B x δ
  change
    (k4ASNY A B x δ)^2+(k4ASNX A x δ)*(k4ASNY A B x δ)*x+
      B*(k4ASNY A B x δ)*x^3+(k4ASNX A x δ)^3+
      (k4ASC A B+1)*(k4ASNX A x δ)^2*x^2+
      (A+k4ASC A B)*(k4ASNX A x δ)*x^4+
      (B*(A+k4ASC A B)+A^2)*x^6 =
    ((k4ASD x)^2*δ+B*x^2*k4ASD x+
      A*x*(x+1)*k4ASD x+A^2*x^2*k4ASD x)*
      (k4ASD x*(δ^2+δ)+(A+B)*x^2+A*x) at hfac
  rw [hfac] at hP
  have hH : k4ASD x*(δ^2+δ)+(A+B)*x^2+A*x=0 :=
    (mul_eq_zero.mp hP).resolve_left hR
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  linear_combination hH + (-((A+B)*x^2+A*x))*h2

theorem k4ASWeierstrass_generic_point_has_source
    [Fintype K] [Algebra (ZMod 2) K]
    (n : ℕ) (hn : Odd n)
    (hfinrank : Module.finrank (ZMod 2) K=n)
    (A B X Y : K)
    (hW : k4ASReverseWeierstrassRhs A B X Y)
    (hXC : X+k4ASC A B ≠ 0)
    (hT : Y+A+k4ASC A B ≠ 0) :
    ∃ x δ : K,
      x ≠ 0 ∧
      k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x ∧
      k4ASWeierstrassX A x δ=X ∧
      k4ASWeierstrassY A B x δ=Y := by
  let x := (X+k4ASC A B)/(Y+A+k4ASC A B)
  have hx : x ≠ 0 := div_ne_zero hXC hT
  have hD : k4ASD x ≠ 0 :=
    k4ASD_ne_zero_of_odd_finrank n hn hfinrank x
  let δ := (X*x^2+A*x*k4ASD x+A*x^3)/(k4ASD x)
  have hDδ : k4ASD x*δ=X*x^2+A*x*k4ASD x+A*x^3 := by
    dsimp [δ]
    field_simp [hD]
  have hNX : k4ASNX A x δ=X*x^2 := by
    have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
    calc
      k4ASNX A x δ = k4ASD x*δ+k4ASD x*(A*x)+A*x^3 := by
        dsimp [k4ASNX]
        ring
      _ = X*x^2+A*x*k4ASD x+A*x^3+
          k4ASD x*(A*x)+A*x^3 := by rw [hDδ]
      _ = X*x^2 := by
        ring_nf
        linear_combination (A*x*k4ASD x+A*x^3)*h2
  have hX : k4ASWeierstrassX A x δ=X := by
    dsimp [k4ASWeierstrassX]
    rw [hNX]
    field_simp [hx]
  have hrel : X+k4ASC A B=x*(Y+A+k4ASC A B) := by
    dsimp [x]
    field_simp [hT]
  have hR : (k4ASD x)^2*δ+B*x^2*k4ASD x+
      A*x*(x+1)*k4ASD x+A^2*x^2*k4ASD x ≠ 0 := by
    rw [k4ASWeierstrass_inverse_denominator_factor A B x δ hx]
    rw [hX]
    exact mul_ne_zero (mul_ne_zero hD (pow_ne_zero 2 hx)) hXC
  have hsource := k4ASWeierstrass_inverse_recovers_source
    A B x δ X Y hx hR hX.symm hrel hW
  have hY : k4ASWeierstrassY A B x δ=Y := by
    have hcoord := k4ASWeierstrass_coordinate_relation A B x δ hx
    rw [hX] at hcoord
    have hm : x*(k4ASWeierstrassY A B x δ+A+k4ASC A B)=
        x*(Y+A+k4ASC A B) := hcoord.symm.trans hrel
    have heq := mul_left_cancel₀ hx hm
    calc
      k4ASWeierstrassY A B x δ=
          (k4ASWeierstrassY A B x δ+A+k4ASC A B)-
            (A+k4ASC A B) := by ring
      _=(Y+A+k4ASC A B)-(A+k4ASC A B) := by rw [heq]
      _=Y := by ring
  exact ⟨x,δ,hx,hsource,hX,hY⟩

#print axioms k4ASWeierstrass_equation_implies_numerator_zero
#print axioms k4ASW_ySpecial_iff_factor
#print axioms k4ASW_xSpecial_iff_factor
#print axioms k4ASW_ySpecial_points_classified
#print axioms k4ASW_xSpecial_points_classified
#print axioms k4ASWeierstrass_inverse_recovers_source
#print axioms k4ASWeierstrass_generic_point_has_source

end Carlet
