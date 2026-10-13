# Formal coverage

## Frozen target

Source: [`FOUNDATIONS.md`](../FOUNDATIONS.md), baseline commit `1d7e494ec3e44d5361bd3c3264957290ed6bb6b0`.
The definitions and theorem hypotheses in `Foundations.lean` are the acceptance target.
The pinned Lean/Mathlib build and strict axiom audit must pass before treating a
statement as machine-checked. The workflow records the exact tested commit/run.

## Statements covered

The continuous integrating-factor bound under explicit endpoint continuity and interior derivative hypotheses; exponential-rate decay for a positive rate; weak and strict gradient-step decrease conditional on the stated quadratic upper model; zero relational effect exactly when the modeled states agree.

## Limits and unresolved obligations

Deriving the quadratic upper model from a Lipschitz gradient, KKT regularity and the proposed field dynamics remain separate obligations. Contextual invariance and scientific usefulness remain empirical hypotheses. No universal correction principle is assumed or proved.

## Evidence discipline

These are established algebra, analysis and finite-dimensional mathematics,
not a novelty claim. Formal proofs establish only their stated hypotheses and
conclusions. Computational regression tests are software checks, not independent
experimental evidence. No theorem uses a claimed physical interpretation as a
premise. No custom axioms, `sorry`, or native-evaluation trust exception is allowed.
No new animal operation is invented or claimed to have been executed.

The first evidence status is **unresolved** until the exact-commit workflow
succeeds; thereafter only the covered formal statements are **demonstrated**.
Scientific applicability remains a **hypothesis/postulate** unless separately tested.
