# Carlet Conjecture: Complete Parity Results, Lean Formalization, and Proof Candidate

This repository includes (1) a paper proving the full admissible odd- and even-degree ranges, (2) the Lean 4 development and its complete-build/audit evidence, and (3) Wang Quanzhi's August 2026 proof-candidate manuscript. The Lean proof route in the paper is separate from the candidate manuscript's geometric/cohomological route.

## Results and exact scope

For odd `n`, if `3 <= k` and `k + 3 <= n`, then every finite field `K` of characteristic 2 and cardinality `2^n` has a `k`-dimensional F2-linear subspace whose nonzero inverses sum to zero. This is the original proposition `OddCarletConjecture` in `formalization/Carlet/Statement.lean`, proved by `oddCarletConjecture_main`.

For even `n`, if `2 <= k` and `k + 2 <= n`, the same conclusion holds for every such finite field. The Lean theorem is `evenDegreeCarlet_unconditional` in `formalization/Carlet/EvenDegree.lean`. The two declarations imply the paper's combined parity-dependent theorem.

## Lean verification

The latest full default build and independent verification report (2026-11-07) records 327 modules, 1,188 audited declarations, zero compiler warnings, matching source/OLean hashes, and axiom sets for both main results limited to `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or custom unproved axiom occurs in either result's audited dependency chain. See `formalization/verified_build_summary.json`, `formalization/final_theorem_audit.json`, and `formalization/build_receipt.json`.

The proof-paper PDFs and TeX sources are in [`paper/lean-formalization/`](paper/lean-formalization/). Reproduction commands are:

```powershell
cd formalization
python -I build.py
python -I verify_build.py
python -I audit_final_theorem.py
```

The recorded environment uses Lean 4.33.0, a pinned Mathlib source baseline, local compatible caches, and the included AINTLIB Hasse-Weil source. A clean-room build from a fresh machine has not been demonstrated; the checked receipt reports the actual full build and source/OLean audit, not a fresh external reproduction.

## The supplied proof-candidate manuscript

`paper/original-proof-candidate/` contains the Chinese and English PDF editions, TeX sources and the supplied finite-certificate verifier. Both manuscripts now include a separate complete even-degree proof supplement. The odd-degree reciprocal-geometric argument remains a proof candidate undergoing independent review; the current Lean proof establishes the odd and even theorem statements through the separate route described in `paper/lean-formalization/`, and does not certify that candidate route. The finite certificates verify only their stated finite cases.

## Licensing

Original Lean code and repository-authored code are offered under the MIT License in [`LICENSE`](LICENSE). Papers and manuscript materials in `paper/` are offered under CC BY 4.0 as described in [`paper/LICENSE.md`](paper/LICENSE.md). Vendored AINTLIB material retains its Apache-2.0 notice. Third-party sources retain their own notices.
