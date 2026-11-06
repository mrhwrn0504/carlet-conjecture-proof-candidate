import Carlet.Frobenius19Base
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 524288
example : r7_19^2 + r8_19 = f19 * q7_19 := by
  unfold r7_19 r8_19 f19 q7_19
  ring_nf <;> simp [c2_19, c3_19, c4_19, c5_19, c6_19, c7_19, c8_19, c9_19, c10_19, c11_19, c12_19, c13_19, c14_19, c15_19, c16_19, c17_19, c18_19, c19_19, c20_19, c21_19, c22_19, c23_19, c24_19]
