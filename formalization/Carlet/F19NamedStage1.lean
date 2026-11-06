import Carlet.F19NamedTail
set_option maxRecDepth 524288
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Polynomial
noncomputable section
lemma square_step_19 {a r s q:P19Frob} (h:f19Frob∣a+r) (hr:r^2+s=f19Frob*q) : f19Frob∣a^2+s := by
  have h1:f19Frob∣(a+r)^2 := dvd_pow h (by norm_num)
  have h2:f19Frob∣r^2+s := ⟨q,hr⟩
  have h3:f19Frob∣(a+r)^2+(r^2+s) := dvd_add h1 h2
  have heq:(a+r)^2+(r^2+s)=a^2+s := by ring_nf <;> simp [c2_19]
  rw [heq] at h3
  exact h3
lemma Xpow_square_19 (m:Nat) : ((X:P19Frob)^(2^m))^2=(X:P19Frob)^(2^(m+1)) := by rw [←pow_mul,Nat.pow_succ]
theorem f19_dvd_frob_stage7 : f19Frob∣(X:P19Frob)^(2^7:Nat)+r7_19 := by
  have h0:f19Frob∣(X:P19Frob)^(2^0:Nat)+r0_19 := by
    have hx:(X:P19Frob)+X=0 := by have ht:=congrArg (fun z:P19Frob=>z*X) c2_19; simpa [two_mul] using ht
    have he:(X:P19Frob)^(2^0:Nat)+r0_19=0 := by simpa [r0_19] using hx
    rw [he]; exact dvd_zero f19Frob
  have h1:f19Frob∣(X:P19Frob)^(2^1:Nat)+r1_19 := by
    have h:=square_step_19 h0 rel0_19
    simpa only [Xpow_square_19] using h
  have h2:f19Frob∣(X:P19Frob)^(2^2:Nat)+r2_19 := by
    have h:=square_step_19 h1 rel1_19
    simpa only [Xpow_square_19] using h
  have h3:f19Frob∣(X:P19Frob)^(2^3:Nat)+r3_19 := by
    have h:=square_step_19 h2 rel2_19
    simpa only [Xpow_square_19] using h
  have h4:f19Frob∣(X:P19Frob)^(2^4:Nat)+r4_19 := by
    have h:=square_step_19 h3 rel3_19
    simpa only [Xpow_square_19] using h
  have h5:f19Frob∣(X:P19Frob)^(2^5:Nat)+r5_19 := by
    have h:=square_step_19 h4 rel4_19
    simpa only [Xpow_square_19] using h
  have h6:f19Frob∣(X:P19Frob)^(2^6:Nat)+r6_19 := by
    have h:=square_step_19 h5 rel5_19
    simpa only [Xpow_square_19] using h
  have h7:f19Frob∣(X:P19Frob)^(2^7:Nat)+r7_19 := by
    have h:=square_step_19 h6 rel6_19
    simpa only [Xpow_square_19] using h
  exact h7
