# Carlet Conjecture: Odd-Degree Formalization and Proof Candidate

This repository keeps two related but logically separate works together. The first is Wang Quanzhi's August 2026 proof-candidate manuscript. The second is an independent Lean 4 formalization of the odd-degree statement. The Lean development is **not a translation or certification of the manuscript's reciprocal-geometry argument**.

## Results and scope

The Lean paper states the following result. Let K be any finite field of characteristic 2 with |K| = 2^n. If n is odd and 3 <= k <= n - 3, then there is a k-dimensional linear subspace over F_2 contained in K such that the sum of the inverses of its nonzero elements is zero:

\[
  \sum_{x\in E\setminus\{0\}}x^{-1}=0.
\]

The included prior build and audit receipts record a complete Lean proof of this odd-degree statement, with the original quantifiers and the axiom set propext, Classical.choice, and Quot.sound. This package assembly did **not** rerun Lean verification. The receipts are historical evidence from the recorded 2026-11-06 build; consult their source hashes and audit output before relying on them for a later source revision. No claim is made here for even n.

## Contents

- [`paper/lean-formalization/`](paper/lean-formalization/): the English and Chinese papers describing the Lean proof route, with their TeX sources and PDFs.
- [`paper/original-proof-candidate/`](paper/original-proof-candidate/): revised Chinese and English PDF editions of Wang Quanzhi's proof-candidate manuscript, their TeX sources, and the supplied finite-certificate verifier and archive. The DOCX source files are not included in the release package.
- [`formalization/`](formalization/): Lean sources, build and audit scripts, prior receipts, and the included Hasse--Weil dependency sources.
- [`CITATION.cff`](CITATION.cff): citation metadata.

## Important distinction about the candidate manuscript

The revised manuscript calls its main result a **proof candidate** and says that its new reciprocal-geometric arguments in Sections 4--10 require independent line-by-line review. The three finite certificates have been checked by the supplied exact verifier; that finite computation does not certify the general geometric proof. The Chinese edition is re-typeset and clarified; the English edition preserves the supplied English proof body and adds revised front matter and clarifications. Neither candidate manuscript is certified by the Lean development in this repository. See its accompanying README for exact scope and provenance.

The Lean paper follows a separate route based on subspace-polynomial coefficients, elliptic-curve point counts, norm-one curve counts, and a high-dimensional recurrence. Its formalization proves the odd-degree statement, not the candidate manuscript's chain of geometric lemmas. The two works should be cited and assessed separately.

## Rebuilding

The formalization directory includes `build.py`, `verify_build.py`, and theorem-audit scripts. The recorded environment used Lean 4.33.0, a pinned Mathlib source baseline, local caches, and the included patched AINTLIB Hasse--Weil source. A clean-room, relocatable build from this release directory has not been demonstrated; the current scripts may depend on machine-local paths and caches. The checked-in receipts are not a substitute for reproducing a build from a fresh environment.

To inspect the recorded result, see `formalization/verified_build_summary.json`, `formalization/final_theorem_audit.json`, and `formalization/build_receipt.json`. Do not describe the manuscript's candidate proof as Lean-verified on the basis of those receipts.

## Licensing

Original Lean code and repository-authored code are offered under the MIT License in [`LICENSE`](LICENSE). Papers and manuscript materials in `paper/` are offered under CC BY 4.0 as described in [`paper/LICENSE.md`](paper/LICENSE.md). The vendored AINTLIB material retains its Apache-2.0 license in `formalization/vendor/aintlib/LICENSE`. Third-party sources retain their own notices. The candidate manuscript's English PDF and verifier files are included from the supplied materials.
