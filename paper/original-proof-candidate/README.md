# Carlet Conjecture proof-candidate manuscript

This directory contains a revised, journal-style Chinese edition and an English edition of Wang Quanzhi's August 2026 proof-candidate manuscript. The mathematical argument is the author's reciprocal-geometric route. It is separate from the Lean formalization elsewhere in this repository.

## Status

The three finite-field certificates for `(n,k) = (29,13), (29,14), (31,14)` have been independently checked by exact computation. That does not certify the general argument in Sections 4--10. The odd-degree reciprocal-geometric proof remains a candidate and requires independent specialist line-by-line review; that route has not been formalized in Lean. A new, separate even-degree supplement proves the full even range `n >= 4` even and `2 <= k <= n-2`; it follows the finite-field counting and subspace-polynomial route formalized in this repository. The supplement does not certify the odd-degree candidate argument.

## Revised editions

- `carlet-proof-candidate-zh.pdf` — Chinese article, re-typeset in a mathematical-paper layout, now with a full even-degree proof section before the bibliography. The odd-degree candidate, finite certificates, verification method, thresholds, references, and three mathematical clarifications are retained.
- `carlet-proof-candidate-en.pdf` — English title page and revision note, the supplied English proof text, and the even-degree proof supplement appended as a separate section. The odd-degree candidate status remains explicit.
- `carlet-proof-candidate-zh.tex`, `carlet-proof-candidate-en-front.tex`, `even-degree-supplement-en.tex` — editable sources for the Chinese edition, English front matter, and English even-degree supplement. The supplied English proof body was provided as PDF, so its original full TeX source is unavailable here.

The first author is Wang Quanzhi. ChatGPT is identified for AI-assisted editorial work. The original source file on the author's G: drive was not modified. The revised release does not include DOCX files, and no output filename contains an author name.

## Reproduction and supplements

The Chinese PDF was built with Tectonic 0.17.0 from its TeX source. The English PDF combines the revised Tectonic front matter, supplied English proof-body pages, and the Tectonic even-degree supplement; the original incomplete author cover was omitted. The supplied `verify_carlet_paper.py` and `verify_carlet_paper.zip` are retained as supplementary material. The verifier was rerun for this revision: all three finite-field certificates, irreducibility checks, ranks, subspace-polynomial coefficients, reciprocal sums, and numerical gateway checks passed. These finite checks do not certify the general odd-degree geometric argument.

The August 2026 manuscript's bibliography is retained. A later preprint is noted for context: K. Cheng, *Counting zero-sum subspaces for the multiplicative inverse function*, arXiv:2610.06445v1, submitted 5 October 2026. Its proof was not audited here, and no priority claim is made.
