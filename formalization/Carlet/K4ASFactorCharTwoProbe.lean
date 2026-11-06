import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Carlet

variable {K : Type*} [Field K] [CharP K 2]

theorem k4AS_numerator_factorization_charTwo (A B x δ : K) :
    let C := A^2 + B
    let D := x^2 + x + 1
    let nx := D*(δ + A*x) + A*x^3
    let ny := D*(δ + A*x + C*x^2) + C*x^4
    let H := D*(δ^2 + δ) + (A+B)*x^2 + A*x
    let Q := x^3*D^2*δ + B*x^5*D + A*x^4*(x+1)*D + A^2*x^5*D
    ny^2*x^3 + nx*ny*x^4 + B*ny*x^6 + nx^3*x^3 +
      (C+1)*nx^2*x^5 + (A+C)*nx*x^7 + (B*(A+C)+A^2)*x^9 = Q*H := by
  dsimp
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcast (n : ℕ) : (n : K) = ((n % 2 : ℕ) : K) := by
    have hn := congrArg (fun z : ℕ => (z : K)) (Nat.mod_add_div n 2)
    have hn' : ((n % 2 : ℕ) : K) + (2 : K) * ((n / 2 : ℕ) : K) = (n : K) := by
      simpa using hn
    calc
      (n : K) = ((n % 2 : ℕ) : K) + (2 : K) * ((n / 2 : ℕ) : K) := hn'.symm
      _ = ((n % 2 : ℕ) : K) := by rw [h2, zero_mul, add_zero]
  have h3 : (3 : K) = 1 := by
    have hc := hcast 3
    norm_num at hc
    exact hc
  have h4 : (4 : K) = 0 := by
    have hc := hcast 4
    norm_num at hc
    exact hc
  have h5 : (5 : K) = 1 := by
    have hc := hcast 5
    norm_num at hc
    exact hc
  have h6 : (6 : K) = 0 := by
    have hc := hcast 6
    norm_num at hc
    exact hc
  have h7 : (7 : K) = 1 := by
    have hc := hcast 7
    norm_num at hc
    exact hc
  have h8 : (8 : K) = 0 := by
    have hc := hcast 8
    norm_num at hc
    exact hc
  have h9 : (9 : K) = 1 := by
    have hc := hcast 9
    norm_num at hc
    exact hc
  have h10 : (10 : K) = 0 := by
    have hc := hcast 10
    norm_num at hc
    exact hc
  have h11 : (11 : K) = 1 := by
    have hc := hcast 11
    norm_num at hc
    exact hc
  have h12 : (12 : K) = 0 := by
    have hc := hcast 12
    norm_num at hc
    exact hc
  have h13 : (13 : K) = 1 := by
    have hc := hcast 13
    norm_num at hc
    exact hc
  have h14 : (14 : K) = 0 := by
    have hc := hcast 14
    norm_num at hc
    exact hc
  have h15 : (15 : K) = 1 := by
    have hc := hcast 15
    norm_num at hc
    exact hc
  have h16 : (16 : K) = 0 := by
    have hc := hcast 16
    norm_num at hc
    exact hc
  have h17 : (17 : K) = 1 := by
    have hc := hcast 17
    norm_num at hc
    exact hc
  have h18 : (18 : K) = 0 := by
    have hc := hcast 18
    norm_num at hc
    exact hc
  have h19 : (19 : K) = 1 := by
    have hc := hcast 19
    norm_num at hc
    exact hc
  have h20 : (20 : K) = 0 := by
    have hc := hcast 20
    norm_num at hc
    exact hc
  have h21 : (21 : K) = 1 := by
    have hc := hcast 21
    norm_num at hc
    exact hc
  have h22 : (22 : K) = 0 := by
    have hc := hcast 22
    norm_num at hc
    exact hc
  have h23 : (23 : K) = 1 := by
    have hc := hcast 23
    norm_num at hc
    exact hc
  have h24 : (24 : K) = 0 := by
    have hc := hcast 24
    norm_num at hc
    exact hc
  have h25 : (25 : K) = 1 := by
    have hc := hcast 25
    norm_num at hc
    exact hc
  have h26 : (26 : K) = 0 := by
    have hc := hcast 26
    norm_num at hc
    exact hc
  have h27 : (27 : K) = 1 := by
    have hc := hcast 27
    norm_num at hc
    exact hc
  have h28 : (28 : K) = 0 := by
    have hc := hcast 28
    norm_num at hc
    exact hc
  have h29 : (29 : K) = 1 := by
    have hc := hcast 29
    norm_num at hc
    exact hc
  have h30 : (30 : K) = 0 := by
    have hc := hcast 30
    norm_num at hc
    exact hc
  have h31 : (31 : K) = 1 := by
    have hc := hcast 31
    norm_num at hc
    exact hc
  have h32 : (32 : K) = 0 := by
    have hc := hcast 32
    norm_num at hc
    exact hc
  have h33 : (33 : K) = 1 := by
    have hc := hcast 33
    norm_num at hc
    exact hc
  have h34 : (34 : K) = 0 := by
    have hc := hcast 34
    norm_num at hc
    exact hc
  have h35 : (35 : K) = 1 := by
    have hc := hcast 35
    norm_num at hc
    exact hc
  have h36 : (36 : K) = 0 := by
    have hc := hcast 36
    norm_num at hc
    exact hc
  have h37 : (37 : K) = 1 := by
    have hc := hcast 37
    norm_num at hc
    exact hc
  have h38 : (38 : K) = 0 := by
    have hc := hcast 38
    norm_num at hc
    exact hc
  have h39 : (39 : K) = 1 := by
    have hc := hcast 39
    norm_num at hc
    exact hc
  have h40 : (40 : K) = 0 := by
    have hc := hcast 40
    norm_num at hc
    exact hc
  have h41 : (41 : K) = 1 := by
    have hc := hcast 41
    norm_num at hc
    exact hc
  have h42 : (42 : K) = 0 := by
    have hc := hcast 42
    norm_num at hc
    exact hc
  have h43 : (43 : K) = 1 := by
    have hc := hcast 43
    norm_num at hc
    exact hc
  have h44 : (44 : K) = 0 := by
    have hc := hcast 44
    norm_num at hc
    exact hc
  have h45 : (45 : K) = 1 := by
    have hc := hcast 45
    norm_num at hc
    exact hc
  have h46 : (46 : K) = 0 := by
    have hc := hcast 46
    norm_num at hc
    exact hc
  have h47 : (47 : K) = 1 := by
    have hc := hcast 47
    norm_num at hc
    exact hc
  ring_nf
  simp_all [h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]

#print axioms k4AS_numerator_factorization_charTwo

end Carlet

