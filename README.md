# Linear crossing families

Companion artifacts for *Linear crossing families via dual levels* by
Tim Gehrunger. This archive contains the Lean formalization of the main theorem
and the original ProofCouncil output from which the manuscript developed.

## Contents

- [`LinearCrossingFamiliesAll.lean`](LinearCrossingFamiliesAll.lean): all project
  definitions and proofs in one file, importing only Mathlib.
- [`ProofCouncil/LinearCrossingFamilies.tex`](ProofCouncil/LinearCrossingFamilies.tex):
  the original ProofCouncil output of 18 September 2026, preserved byte for byte.
  This historical output is distinct from the revised article.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`: the pinned Lean
  environment and dependencies needed to build the proof.
- [`LICENSE`](LICENSE): Creative Commons Attribution 4.0 International.

## Formalized theorem

There is an absolute constant `c > 0` such that every finite set of `n ≥ 2`
points in the real plane, with no three collinear, spans at least `c * n`
segments with pairwise distinct endpoints that cross pairwise in their
relative interiors.

The final declaration is
`LinearCrossingFamilies.linear_crossing_families`.
Its constant is quantified before the point set, and the theorem has no
additional extraction or coordinate assumptions.

The file includes the geometric argument, the fixed-error near-avoidance
extraction (`ε = 1/4`) needed from the Pach–Rubin–Tardos framework, and the
required finite ε-net construction. The full parameter-dependent extraction
theorem and the article's applications to plane trees and spoke sets are
outside the scope of this formalization.

## Build and inspect

Install Lean's [Elan toolchain manager](https://leanprover-community.github.io/get_started.html)
and Git. From this repository's root, run:

```bash
lake exe cache get
lake build
```

The versions are pinned to:

- Lean `leanprover/lean4:v4.34.0`;
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`;
- the transitive dependency revisions in `lake-manifest.json`.

To inspect the proof interactively, open the repository folder in VS Code
with the Lean 4 extension. To check the source and display the final theorem's
axiom dependencies directly, run:

```bash
lake env lean LinearCrossingFamiliesAll.lean
```

## Verification

The combined proof was built and audited on 24 September 2026. The final
theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or added axioms in the source.

An additional [Comparator](https://github.com/leanprover/comparator/tree/v4.34.0)
check passed statement and definition comparison against a separate reference,
the restricted axiom check, and exported-proof replay in Lean's kernel.
This check used Comparator's macOS development mode; Linux process sandboxing
and an additional independent kernel were not part of that run.
The reference used the reviewed geometric definitions and the main theorem's
explicit statement. Mathematical interpretation of the definitions was also
reviewed against the article.

SHA-256 of `LinearCrossingFamiliesAll.lean`:

```text
84d389ca0fd1f6d1dbacd63e74f1624b50841033c037d5e845a8799ac8120bef
```

## Original ProofCouncil output

The mathematical argument originated in an updated version of
[ProofCouncil](https://arxiv.org/abs/2607.09474) during preparations for the
third batch of [First Proof](https://1stproof.org/third-batch.html).
The Lean formalization was prepared with Codex and subsequently audited.

The original workflow recorded 14 model calls and US$32.35794275 in model-API
costs (US$32.36 rounded). This covers the original research, review, and rewrite
workflow; it excludes subsequent manuscript editing, Lean formalization, and
infrastructure costs.

SHA-256 of `ProofCouncil/LinearCrossingFamilies.tex`:

```text
bf577bf90ccd308af043475cf502dd949c5849f6755be392bba28f3ea9fa391c
```

## License and attribution

The materials distributed in this repository are licensed under
[Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
See [`LICENSE`](LICENSE) for the full terms. For attribution, identify
Tim Gehrunger, the article *Linear crossing families via dual levels*, and
this repository. Preserve the identification of the original ProofCouncil
output when redistributing that file, and indicate any modifications.

Lean, Mathlib, and other fetched dependencies retain their own licenses and
are not included in this repository.
