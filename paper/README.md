# Papers in this repository

The repository contains a mathematical proof of the full admissible odd- and even-degree ranges, a Lean 4 formalization paper, and the user's separate proof-candidate manuscript.

## Lean formalization paper

`lean-formalization/main_en.tex` and `main_zh.tex` give the odd-degree result for odd `n` with `3 <= k` and `k + 3 <= n`, and the even-degree result for even `n` with `2 <= k` and `k + 2 <= n`. Both results are proved in Lean for every finite field of the specified cardinality. The paper documents the proof routes, exact theorem declarations, complete default build, independent source/OLean verification, and axiom audit. The latest acceptance record (2026-11-07) reports 327 built modules, 1,188 audited declarations, zero compiler warnings, matching source/OLean hashes, and theorem axioms limited to `propext`, `Classical.choice`, and `Quot.sound`.

The Lean proof route in this paper is distinct from the geometric/cohomological route of the proof-candidate manuscript. The conjecture is formally proved by the repository's current route; line-by-line formalization of the candidate manuscript's specific route remains in progress and is not claimed complete here.

## Revised proof-candidate manuscript

`original-proof-candidate/` contains Chinese and English PDF editions of Wang Quanzhi's August 2026 proof-candidate manuscript, TeX sources, and the supplied finite-certificate verifier. Both editions now include a separate even-degree proof supplement. That supplement follows the repository's formalized counting and subspace-polynomial route and proves the even range for every finite field of order `2^n`. The odd-degree reciprocal-geometric argument remains a candidate under independent specialist review and is not certified by the supplement or by the separate Lean route.

The manuscript itself labels the general reciprocal-geometric proof as a candidate pending independent specialist review. Its three finite certificates pass the exact supplied verifier; that does not certify the general argument or amount to Lean formalization. No DOCX files are distributed. Both editions are detailed in the subdirectory README.

The paper materials are licensed under CC BY 4.0; see [`LICENSE.md`](LICENSE.md) and the [official license text](https://creativecommons.org/licenses/by/4.0/legalcode).
