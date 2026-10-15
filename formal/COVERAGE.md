# Formal coverage

## Frozen target

Source: [FOUNDATIONS.md](../FOUNDATIONS.md), baseline commit
`1d7e494ec3e44d5361bd3c3264957290ed6bb6b0`.
The definitions and hypotheses in `Foundations.lean` are the acceptance target.
The pinned Lean/Mathlib build and strict axiom audit must pass before a statement
is treated as machine-checked. [CI](../.github/workflows/lean.yml) identifies the
exact tested commit. The original source remains unchanged.

## Covered mathematical statements

| Source topic | Formal result and hypotheses |
|---|---|
| Conditional correction | Endpoint continuity, interior differentiability and the stated differential inequality imply the exponential bound. Positive decay rate implies decay of its exponential factor. This does not prove the inequality for an arbitrary system. |
| Relational effect | With positive regularization, zero effect is equivalent to agreement of coupled and baseline states. |
| Iterative refinement | A genuine globally Lipschitz gradient implies the quadratic upper model by differentiating along a line segment. A step with L > 0 and 0 < alpha < 2/L does not increase the objective; a nonzero gradient gives strict decrease. |
| Constraint harmony | Convex differentiable objectives and finitely many convex differentiable inequality constraints admit necessary and sufficient KKT conditions at a feasible point under Slater's strict-feasibility condition. Multiplier existence is derived. |
| Contextual invariance | The relational-effect ratio is invariant under the same real linear isometry applied to both states. It is also invariant under positive rescaling when its regularizer is scaled consistently. |

The analytic state space is a real Hilbert space, including finite-dimensional
Euclidean states. These are standard mathematical results, not novelty claims.

## KKT proof and acceptance conditions

`convex_slater_multipliers` separates the convex strict upper image of the
objective/constraints from zero. It proves nonnegative multipliers,
complementarity and a global Lagrangian lower bound. Slater's condition excludes
a zero objective multiplier, permitting normalization.

`kkt_necessary_slater` differentiates that Lagrangian along a line through its
minimum and obtains stationarity. `kkt_iff_slater` combines this necessity
result with the existing `kkt_sufficient` theorem.

No multiplier, stationarity condition or supporting inequality is assumed in
the necessity theorem. Slater's condition means an actual point at which every
inequality is strict. Convexity is global; differentiability is required at the
candidate point. Arbitrary finite constraint families, including the empty
family, are allowed. Equality constraints, nonsmooth objectives and nonconvex
global optimality are outside these theorems. Necessity is not claimed when
strict feasibility fails.

## Remaining specification work

The proposed continuum field equations still lack a fixed spatial domain,
coefficient/kernel assumptions, function spaces, boundary/initial data and a
chosen existence, stability or conservation conclusion. Selecting these data
changes the mathematical problem. The finite-dimensional theorems do not
establish those PDE results.

The two contextual results specify both transformation and observable. Other
transformations or observables require their own definitions and proofs.
Covariance of an unspecified scientific H is not inferred.

No universal correction principle, physical field law, fifth force or empirical
AGI claim follows from the formalization. Scientific applicability remains a
hypothesis until independently tested.

## Evidence discipline

Every project declaration, including private declarations, is audited against
`propext`, `Classical.choice` and `Quot.sound` only. Rejection controls exercise
public/private axioms, placeholders and native-evaluation oracles.
The evidence status is **unresolved** until the exact commit passes;
thereafter only the stated mathematical results are **demonstrated**.
