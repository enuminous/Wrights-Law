# Formal coverage

## Frozen target

Source: [`FOUNDATIONS.md`](../FOUNDATIONS.md), baseline commit `1d7e494ec3e44d5361bd3c3264957290ed6bb6b0`.
The definitions and theorem hypotheses in `Foundations.lean` are the acceptance target.
The pinned Lean/Mathlib build and strict axiom audit must pass before treating a
statement as machine-checked. The workflow records the exact tested commit/run.

## Statements covered

The original continuous integrating-factor bound, exponential-rate decay, algebraic descent implications, and zero relational-effect criterion remain covered.

The new analytic derivations use a real Hilbert space, so they include the finite-dimensional states in `FOUNDATIONS.md`:

| Theorem | Established conclusion |
|---|---|
| `quadratic_upper_bound_of_lipschitz_gradient` | A genuine globally L-Lipschitz gradient implies the quadratic upper model, proved by differentiation along a line segment. |
| `gradient_step_bound` | Substituting the negative-gradient step gives the quantitative decrease bound. |
| `gradient_step_descent` | For L > 0 and 0 < α < 2/L the objective does not increase, including at stationary points. |
| `gradient_step_strict_descent` | Under the same conditions, a nonzero gradient gives strict decrease. |
| `convex_gradient_support` | Convexity and an actual gradient imply the first-order supporting inequality. |
| `kkt_sufficient` | For a convex differentiable objective and finitely many convex differentiable inequality constraints, feasibility, nonnegative multipliers, complementarity and stationarity imply global optimality. |

The gradient model is derived rather than assumed in the new theorems. The KKT proof derives the supporting inequalities from convexity; it does not assume the desired optimality conclusion. The original baseline source remains unchanged.

## Limits and unresolved obligations

The Lipschitz-gradient derivation is closed by this tranche. KKT **necessity**, existence of multipliers and the appropriate constraint qualification remain open; the sufficiency theorem does not establish them. Equality constraints, nonsmooth objectives and nonconvex global optimality are outside this theorem.

The proposed field dynamics still need a fixed spatial domain, coefficient and kernel assumptions, function spaces, boundary/initial conditions, and the claimed existence, stability or conservation property. Those choices determine different mathematical problems. Contextual invariance also needs a specified transformation and observable. Its scientific usefulness remains empirical. No universal correction principle or physical field law is proved.

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
