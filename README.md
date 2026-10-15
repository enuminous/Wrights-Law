# Emergentology and Wright's Law

<!-- ENUMINOUS-NETWORK:START -->
**eNuminous network:** [All repositories](https://enuminous.github.io/EFMW/repositories.html) · [EFMW](https://enuminous.github.io/EFMW/) · [102 equations](https://github.com/enuminous/Monolithic_102_EFMW) · [165 triplets](https://enuminous.github.io/FieldSpace/) · [Zoo](https://enuminous.github.io/Tortoise/) · [Lean](https://enuminous.github.io/Aristotle-102-Monolithic-Lean/) · [Engine](https://enuminous.github.io/Archimedes-Engine/) · [Papers](https://enuminous.github.io/medium/papers-essays-index.html) · [Audit](https://github.com/enuminous/EFMW_Post156_Zoo_Audit/blob/main/portfolio/INTERLOCK_AUDIT.md)

[Repository](https://github.com/enuminous/Wrights-Law) · [Published page](https://enuminous.github.io/Wrights-Law/)

<details>
<summary>Recent repositories (9)</summary>

- [Oroboros](https://github.com/enuminous/Oroboros) · [README](https://github.com/enuminous/Oroboros/blob/main/README.md) · [Page](https://enuminous.github.io/Oroboros/)
- [P-NP](https://github.com/enuminous/P-NP) · [README](https://github.com/enuminous/P-NP/blob/main/README.md) · [Page](https://enuminous.github.io/P-NP/)
- [Research-Program](https://github.com/enuminous/Research-Program) · [README](https://github.com/enuminous/Research-Program/blob/main/README.md) · [Page](https://enuminous.github.io/Research-Program/)
- [I-Have-Guts](https://github.com/enuminous/I-Have-Guts) · [README](https://github.com/enuminous/I-Have-Guts/blob/main/README.md) · [Page](https://enuminous.github.io/I-Have-Guts/)
- [Wrights-Law](https://github.com/enuminous/Wrights-Law) · [README](https://github.com/enuminous/Wrights-Law/blob/main/README.md) · [Page](https://enuminous.github.io/Wrights-Law/)
- [Aristotle-eNuminous](https://github.com/enuminous/Aristotle-eNuminous) · [README](https://github.com/enuminous/Aristotle-eNuminous/blob/main/README.md) · [Page](https://enuminous.github.io/Aristotle-eNuminous/)
- [Multiverse-Simulator](https://github.com/enuminous/Multiverse-Simulator) · [README](https://github.com/enuminous/Multiverse-Simulator/blob/main/README.md) · [Page](https://enuminous.github.io/Multiverse-Simulator/)
- [accelerando-8192](https://github.com/enuminous/accelerando-8192) · [README](https://github.com/enuminous/accelerando-8192/blob/main/README.md) · [Page source](https://github.com/enuminous/accelerando-8192/blob/main/docs/index.html)
- [Codex-888](https://github.com/enuminous/Codex-888) · [README](https://github.com/enuminous/Codex-888/blob/main/README.md) · [Page](https://enuminous.github.io/Codex-888/)

</details>

<details>
<summary>Repository indexes (1)</summary>

- [index.html](https://github.com/enuminous/Wrights-Law/blob/main/index.html) · [Open page](https://enuminous.github.io/Wrights-Law/index.html)

</details>
<!-- ENUMINOUS-NETWORK:END -->

Research and formal-verification package based on Matthew Chenoweth Wright's January 28, 2025 paper (with Millie Sievert).

**Status: proposed mathematical framework, not a verified universal law or new fundamental force.**

## Run

```sh
pip install -r requirements.txt
python -m unittest -v test_emerg001.py
python emerg001.py --seeds 12 --out results.csv
```

Outputs `results.csv` and `results.csv.summary.json`. Nothing is presented as experimentally confirmed in advance. The Lean package is in `formal/`.

## Contents

- `index.html`: GitHub Pages landing page
- `FOUNDATIONS.md`: axioms, mathematical definitions, conditional theorems
- `PROTOCOL.md`: EMERG-001 experiment design and caveats
- `emerg001.py`: paired stochastic network simulation
- `test_emerg001.py`: automated checks
- `SOURCE.md`: source provenance
- `requirements.txt`: dependencies

The published repository is [enuminous/Wrights-Law](https://github.com/enuminous/Wrights-Law).

## Lean 4 verification

The pinned [formal package](formal/VERIFICATION.md) contains kernel-checked mathematical
statements with an explicit [coverage and obligation ledger](formal/COVERAGE.md).
The `Lean verification` workflow builds the package and tests its strict axiom audit.
The workflow result for a commit, rather than this link alone, establishes compilation.

The [formal coverage](formal/COVERAGE.md) includes a quadratic upper bound derived from a Lipschitz gradient, weak and strict gradient-step decrease, and necessary and sufficient convex KKT conditions under Slater's condition. Multiplier existence is proved. Linear-isometry and consistent positive-scaling invariances are proved for the relational-effect ratio. The field realization below fixes a precise periodic specification; more general field and coupling claims remain open.

The [periodic-field realization](formal/PeriodicField.lean) now supplies an exact
finite cosine-sector solution of the diffusion/damping/nonlocal equation,
uniqueness, periodicity and a quantitative stability condition. The constant
mode supplies a counterexample when feedback exceeds damping. See the
[coverage ledger](formal/COVERAGE.md) for its fixed domain and remaining limits.
