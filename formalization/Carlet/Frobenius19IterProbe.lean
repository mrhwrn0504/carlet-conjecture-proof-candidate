import Carlet.Frobenius19Stage1
open Polynomial
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
def iterFrob19 : Nat → P19
  | 0 => X
  | m+1 => (iterFrob19 m)^2
lemma iterFrob19_eq (m : Nat) : iterFrob19 m = (X:P19)^(2^m) := by
  induction m with
  | zero => simp [iterFrob19]
  | succ m ih => rw [iterFrob19, ih, Xpow_square_19]
theorem f19_dvd_iterFrob : f19 ∣ iterFrob19 19 + X := by
  have h0 : f19 ∣ iterFrob19 0 + r0_19 := by
    have hx : (X:P19)+X=0 := by
      have ht:=congrArg (fun z:P19=>z*X) c2_19
      simpa [two_mul] using ht
    change f19 ∣ (X:P19)+r0_19
    simp [r0_19, hx]
  have h1 : f19 ∣ iterFrob19 1 + r1_19 := by
    change f19 ∣ (iterFrob19 0)^2 + r1_19
    exact square_step_19 h0 rel0_19
  have h2 : f19 ∣ iterFrob19 2 + r2_19 := by
    change f19 ∣ (iterFrob19 1)^2 + r2_19
    exact square_step_19 h1 rel1_19
  have h3 : f19 ∣ iterFrob19 3 + r3_19 := by
    change f19 ∣ (iterFrob19 2)^2 + r3_19
    exact square_step_19 h2 rel2_19
  have h4 : f19 ∣ iterFrob19 4 + r4_19 := by
    change f19 ∣ (iterFrob19 3)^2 + r4_19
    exact square_step_19 h3 rel3_19
  have h5 : f19 ∣ iterFrob19 5 + r5_19 := by
    change f19 ∣ (iterFrob19 4)^2 + r5_19
    exact square_step_19 h4 rel4_19
  have h6 : f19 ∣ iterFrob19 6 + r6_19 := by
    change f19 ∣ (iterFrob19 5)^2 + r6_19
    exact square_step_19 h5 rel5_19
  have h7 : f19 ∣ iterFrob19 7 + r7_19 := by
    change f19 ∣ (iterFrob19 6)^2 + r7_19
    exact square_step_19 h6 rel6_19
  have h8 : f19 ∣ iterFrob19 8 + r8_19 := by
    change f19 ∣ (iterFrob19 7)^2 + r8_19
    exact square_step_19 h7 rel7_19
  have h9 : f19 ∣ iterFrob19 9 + r9_19 := by
    change f19 ∣ (iterFrob19 8)^2 + r9_19
    exact square_step_19 h8 rel8_19
  have h10 : f19 ∣ iterFrob19 10 + r10_19 := by
    change f19 ∣ (iterFrob19 9)^2 + r10_19
    exact square_step_19 h9 rel9_19
  have h11 : f19 ∣ iterFrob19 11 + r11_19 := by
    change f19 ∣ (iterFrob19 10)^2 + r11_19
    exact square_step_19 h10 rel10_19
  have h12 : f19 ∣ iterFrob19 12 + r12_19 := by
    change f19 ∣ (iterFrob19 11)^2 + r12_19
    exact square_step_19 h11 rel11_19
  have h13 : f19 ∣ iterFrob19 13 + r13_19 := by
    change f19 ∣ (iterFrob19 12)^2 + r13_19
    exact square_step_19 h12 rel12_19
  have h14 : f19 ∣ iterFrob19 14 + r14_19 := by
    change f19 ∣ (iterFrob19 13)^2 + r14_19
    exact square_step_19 h13 rel13_19
  have h15 : f19 ∣ iterFrob19 15 + r15_19 := by
    change f19 ∣ (iterFrob19 14)^2 + r15_19
    exact square_step_19 h14 rel14_19
  have h16 : f19 ∣ iterFrob19 16 + r16_19 := by
    change f19 ∣ (iterFrob19 15)^2 + r16_19
    exact square_step_19 h15 rel15_19
  have h17 : f19 ∣ iterFrob19 17 + r17_19 := by
    change f19 ∣ (iterFrob19 16)^2 + r17_19
    exact square_step_19 h16 rel16_19
  have h18 : f19 ∣ iterFrob19 18 + r18_19 := by
    change f19 ∣ (iterFrob19 17)^2 + r18_19
    exact square_step_19 h17 rel17_19
  have h19 : f19 ∣ iterFrob19 19 + r19_19 := by
    change f19 ∣ (iterFrob19 18)^2 + r19_19
    exact square_step_19 h18 rel18_19
  simpa only [r19_19, pow_one] using h19
#print axioms f19_dvd_iterFrob
#print axioms iterFrob19_eq
