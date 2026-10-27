# Emergentology and Wright's Law

<!-- ENUMINOUS-UNIFIED-NAV:START -->
## Repository navigation

**eNuminous network:** [All public repositories](https://github.com/enuminous/EFMW/blob/main/REPOSITORY_NAVIGATION.md) · [EFMW](https://github.com/enuminous/EFMW) · [102 equations](https://github.com/enuminous/Monolithic_102_EFMW) · [Frozen Lean](https://github.com/enuminous/Monolithic-102-Zoo-Lean4) · [Zoo](https://github.com/enuminous/Tortoise) · [Papers](https://github.com/enuminous/papers) · [Quantum geometry](https://github.com/enuminous/Base888-Quantum-Geometry)

**This project:** [Repository home](https://github.com/enuminous/Wrights-Law) · [Subject index](https://github.com/enuminous/EFMW/blob/main/REPOSITORY_NAVIGATION.md#papers-publications-and-creative-work) · [Published site](https://enuminous.github.io/Wrights-Law/) · [Web application](index.html)

<details open>
<summary><strong>On this page</strong></summary>

- [Run](#run)
- [Contents](#contents)
- [Lean 4 verification](#lean-4-verification)


</details>

**Related repositories:** [I-Have-Guts](https://github.com/enuminous/I-Have-Guts) · [Research-Program](https://github.com/enuminous/Research-Program) · [Extrauniversal-Warren-Report](https://github.com/enuminous/Extrauniversal-Warren-Report) · [Mathematics-and-Elite-Squad-Dynamics](https://github.com/enuminous/Mathematics-and-Elite-Squad-Dynamics) · [papers](https://github.com/enuminous/papers) · [EFMW](https://github.com/enuminous/EFMW)

> **Evidence boundary:** A link between projects is navigation, not an assertion of proven equivalence, experimental validation, or shared authorship. See each repository’s own status and review notes.
<!-- ENUMINOUS-UNIFIED-NAV:END -->


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
