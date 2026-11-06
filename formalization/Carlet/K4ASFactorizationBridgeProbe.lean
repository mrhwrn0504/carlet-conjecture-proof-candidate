import Carlet.K4ASFactorCharTwoProbe

namespace Carlet

variable {K : Type*} [Field K] [CharP K 2]

theorem k4AS_numerator_factorization_six (A B x δ : K) :
    let C := A^2+B
    let D := x^2+x+1
    let nx := D*(δ+A*x)+A*x^3
    let ny := D*(δ+A*x+C*x^2)+C*x^4
    let H := D*(δ^2+δ)+(A+B)*x^2+A*x
    let R := D^2*δ+B*x^2*D+A*x*(x+1)*D+A^2*x^2*D
    ny^2+nx*ny*x+B*ny*x^3+nx^3+
      (C+1)*nx^2*x^2+(A+C)*nx*x^4+
      (B*(A+C)+A^2)*x^6 = R*H := by
  dsimp
  let C := A^2+B
  let D := x^2+x+1
  let nx := D*(δ+A*x)+A*x^3
  let ny := D*(δ+A*x+C*x^2)+C*x^4
  let H := D*(δ^2+δ)+(A+B)*x^2+A*x
  let R := D^2*δ+B*x^2*D+A*x*(x+1)*D+A^2*x^2*D
  let P6 := ny^2+nx*ny*x+B*ny*x^3+nx^3+
      (C+1)*nx^2*x^2+(A+C)*nx*x^4+
      (B*(A+C)+A^2)*x^6
  have hfact := k4AS_numerator_factorization_charTwo A B x δ
  change
    (ny^2*x^3+nx*ny*x^4+B*ny*x^6+nx^3*x^3+
      (C+1)*nx^2*x^5+(A+C)*nx*x^7+
      (B*(A+C)+A^2)*x^9)=
      (x^3*D^2*δ+B*x^5*D+A*x^4*(x+1)*D+A^2*x^5*D)*H at hfact
  by_cases hx : x = 0
  · subst x
    ring
  · have hleft : ny^2*x^3+nx*ny*x^4+B*ny*x^6+nx^3*x^3+
        (C+1)*nx^2*x^5+(A+C)*nx*x^7+
        (B*(A+C)+A^2)*x^9 = x^3*P6 := by
      dsimp [P6]
      ring
    have hright :
        (x^3*D^2*δ+B*x^5*D+A*x^4*(x+1)*D+A^2*x^5*D)*H =
          x^3*(R*H) := by
      dsimp [R]
      ring
    have hmul : x^3*P6=x^3*(R*H) := by
      calc
        x^3*P6 = ny^2*x^3+nx*ny*x^4+B*ny*x^6+nx^3*x^3+
            (C+1)*nx^2*x^5+(A+C)*nx*x^7+
            (B*(A+C)+A^2)*x^9 := hleft.symm
        _ = (x^3*D^2*δ+B*x^5*D+A*x^4*(x+1)*D+
              A^2*x^5*D)*H := hfact
        _ = x^3*(R*H) := hright
    exact (mul_left_cancel₀ (pow_ne_zero 3 hx) hmul)

#print axioms k4AS_numerator_factorization_six

end Carlet

