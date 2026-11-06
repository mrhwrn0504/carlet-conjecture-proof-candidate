import Carlet.K4ASFactorizationBridgeProbe

noncomputable section

namespace Carlet

variable {K : Type*} [Field K] [CharP K 2]

def k4ASD (x : K) := x^2+x+1
def k4ASC (A B : K) := A^2+B
def k4ASNX (A x δ : K) := k4ASD x*(δ+A*x)+A*x^3
def k4ASNY (A B x δ : K) :=
  k4ASD x*(δ+A*x+(k4ASC A B)*x^2)+(k4ASC A B)*x^4
def k4ASH (A B x δ : K) :=
  k4ASD x*(δ^2+δ)+(A+B)*x^2+A*x
def k4ASQ (A B x δ : K) :=
  x^3*(k4ASD x)^2*δ+B*x^5*k4ASD x+
    A*x^4*(x+1)*k4ASD x+A^2*x^5*k4ASD x

def k4ASWeierstrassX (A x δ : K) :=
  k4ASNX A x δ / x^2
def k4ASWeierstrassY (A B x δ : K) :=
  k4ASNY A B x δ / x^3

theorem k4ASCurveWeierstrass_equation
    (A B x δ : K) (hx : x ≠ 0)
    (hcurve : k4ASD x*(δ^2+δ)=(A+B)*x^2+A*x) :
    let X := k4ASWeierstrassX A x δ
    let Y := k4ASWeierstrassY A B x δ
    Y^2+X*Y+B*Y = X^3+(k4ASC A B+1)*X^2+
      (A+k4ASC A B)*X+B*(A+k4ASC A B)+A^2 := by
  dsimp
  let C := A^2+B
  let D := x^2+x+1
  let nx := D*(δ+A*x)+A*x^3
  let ny := D*(δ+A*x+C*x^2)+C*x^4
  let H := D*(δ^2+δ)+(A+B)*x^2+A*x
  let R := D^2*δ+B*x^2*D+A*x*(x+1)*D+A^2*x^2*D
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hH : H = 0 := by
    change D*(δ^2+δ)+(A+B)*x^2+A*x=0
    have hcurve' : D*(δ^2+δ)=(A+B)*x^2+A*x := by
      simpa [D, k4ASD] using hcurve
    rw [hcurve']
    ring_nf
    simp [h2]
  have hfac := k4AS_numerator_factorization_six A B x δ
  change
    ny^2+nx*ny*x+B*ny*x^3+nx^3+(C+1)*nx^2*x^2+
      (A+C)*nx*x^4+(B*(A+C)+A^2)*x^6=R*H at hfac
  have hP :
      ny^2+nx*ny*x+B*ny*x^3+nx^3+(C+1)*nx^2*x^2+
        (A+C)*nx*x^4+(B*(A+C)+A^2)*x^6 = 0 := by
    simpa [hH] using hfac
  dsimp [k4ASWeierstrassX, k4ASWeierstrassY]
  field_simp [k4ASWeierstrassX, k4ASWeierstrassY,
    k4ASNX, k4ASNY, k4ASD, k4ASC, hx]
  let L := k4ASNY A B x δ *
    (k4ASNY A B x δ + x*k4ASNX A x δ + x^3*B)
  let W := k4ASNX A x δ *
    (k4ASNX A x δ * (k4ASNX A x δ + x^2*(k4ASC A B+1)) +
      x^4*(A+k4ASC A B)) + x^6*B*(A+k4ASC A B)+x^6*A^2
  change L = W
  have hsum : L+W=0 := by
    dsimp [L, W, k4ASNX, k4ASNY, k4ASD, k4ASC, nx, ny, C, D] at *
    linear_combination hP
  linear_combination hsum + (-W)*h2

theorem k4ASWeierstrass_coordinate_relation
    (A B x δ : K) (hx : x ≠ 0) :
    k4ASWeierstrassX A x δ+k4ASC A B =
      x*(k4ASWeierstrassY A B x δ+A+k4ASC A B) := by
  dsimp [k4ASWeierstrassX, k4ASWeierstrassY]
  field_simp [k4ASNX, k4ASNY, k4ASD, k4ASC, hx]
  have h2 : (2 : K)=0 := CharP.cast_eq_zero K 2
  dsimp [k4ASNX, k4ASNY, k4ASD, k4ASC]
  ring_nf
  simp [h2]

#print axioms k4ASCurveWeierstrass_equation
#print axioms k4ASWeierstrass_coordinate_relation

end Carlet
end

