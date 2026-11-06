# Carlet Conjecture proof-candidate manuscript

This directory contains a revised, journal-style Chinese edition and an English edition of Wang Quanzhi's August 2026 proof-candidate manuscript. The mathematical argument is the author's reciprocal-geometric route. It is separate from the Lean formalization elsewhere in this repository.

## Status

The three finite-field certificates for `(n,k) = (29,13), (29,14), (31,14)` have been independently checked by exact computation. That does not certify the general argument in Sections 4--10. The geometric proof remains a candidate and requires independent specialist line-by-line review; it has not been formalized in Lean. The paper and repository do not present it as a fully certified proof.

## Revised editions

- `carlet-proof-candidate-zh.pdf` — Chinese article, re-typeset in a mathematical-paper layout. The repeated contents material and process-only audit checklist were removed; the proof sections, finite certificates, verification method, thresholds, and references were retained. Three clarifications were added on arbitrary-base-ring definitions, the full compact-support cohomology range, and Frobenius-compatible intersection-complex/duality statements.
- `carlet-proof-candidate-en.pdf` — English title page and revision note, followed by the supplied English proof text. It adds the same three clarifications and a current-literature note without claiming that the cited later preprint has been audited.
- `carlet-proof-candidate-zh.tex`, `carlet-proof-candidate-en-front.tex` — TeX sources for the Chinese edition and English front matter/addendum.

The first author is Wang Quanzhi. ChatGPT is identified for AI-assisted editorial work. The original source file on the author's G: drive was not modified. The revised release does not include DOCX files, and no output filename contains an author name.

## Reproduction and supplements

The Chinese PDF was built with Tectonic 0.17.0 from its TeX source. The English PDF combines the new Tectonic front matter/addendum with the supplied English proof-body pages; the original incomplete author cover was omitted. The supplied `verify_carlet_paper.py` and `verify_carlet_paper.zip` are retained as supplementary material; they were not rerun for this editorial/typesetting revision.

The August 2026 manuscript's bibliography is retained. A later preprint is noted for context: K. Cheng, *Counting zero-sum subspaces for the multiplicative inverse function*, arXiv:2610.06445v1, submitted 5 October 2026. Its proof was not audited here, and no priority claim is made.
