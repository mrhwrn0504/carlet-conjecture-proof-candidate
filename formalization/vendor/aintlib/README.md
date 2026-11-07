# Vendored AINTLIB Hasse dependency

This directory contains the source import closure used for the elliptic-curve Hasse bound in the Carlet proof: 188 Lean modules from the AINTLIB Hasse-Weil project and its `Common` dependencies. Unrelated AINTLIB projects, notes, blueprints, and tools have been omitted.

The vendored source is from the AINTLIB snapshot `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`; the project-specific source adjustments are recorded in `compatibility.patch`. The upstream Apache-2.0 license and notices are retained in `LICENSE`.

Run `python -I vendor/aintlib/rebuild.py 188` from `formalization/` to compile this source closure and write its OLean receipt. The root `build.py` runs this step automatically.
