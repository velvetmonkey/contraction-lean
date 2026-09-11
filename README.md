# contraction-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ContractionLean)
[![Paper](https://img.shields.io/badge/Zenodo-20474762-blue)](https://zenodo.org/records/20474762)

Lean 4 formal proofs of contraction theory: Banach fixed point theorem, geometric convergence rates, composition rules, and Lohmiller-Slotine differential contraction.

**Zero sorry statements.** Zero new axioms.

## What this is, and why it matters

This library formalizes several layers of contraction theory, from Banach fixed points to exponential convergence of trajectories. Its headline theorem, `trajectory_convergence`, proves that two continuous trajectories approach each other at rate `exp(-mu*t)` when their distance is differentiable and obeys the contraction differential inequality.

The explicit rate is obtained through a machine-checked Gronwall argument: the distance multiplied by `exp(mu*t)` is shown to be nonincreasing. The library also wraps Mathlib's contraction mapping machinery to prove a unique fixed point, convergence of iterates with a geometric bound, and composition and iteration rules.

The scope of the differential result is narrower than a full Lohmiller-Slotine formalization. The distance inequality is an assumption. The development does not derive it from a symmetric-Jacobian condition, construct ODE solutions, or prove that a given nonlinear system satisfies the required contraction condition.

## Background and motivation

Contraction theory (Lohmiller and Slotine, 1998) provides a unified framework for proving exponential convergence of nonlinear dynamical systems. A contracting system forgets its initial conditions at an exponential rate -- any two trajectories converge toward each other regardless of where they started. This is a stronger and more composable property than Lyapunov stability.

Contraction theory underlies distributed synchronisation, neural dynamics, reinforcement learning, and control theory. This library machine-checks the core results: Banach fixed point with explicit rates, composition rules for building contracting systems, and the Lohmiller-Slotine differential (Jacobian) condition for ODEs.

## Project structure

```
ContractionLean/
├── Defs.lean                    — IsContracting c f (wraps Mathlib's ContractingWith), basic API
├── BanachFixed.lean             — Unique fixed point, geometric convergence, iterate convergence
├── CompositionRules.lean        — Composition and iteration of contracting maps
└── DifferentialContraction.lean — Derivative-based contraction, Gronwall decay, trajectory convergence
ContractionLean.lean             — Root module re-exporting all four
```

## Theorem inventory

### Layer 1 — Definitions and metric contraction

| # | Name | Statement |
|---|------|-----------|
| 1 | `IsContracting` | c < 1 and f is c-Lipschitz (wraps `ContractingWith`) |
| 2 | `exists_unique_fixedPoint` | Unique fixed point ∃! x*, f(x*) = x* |
| 3 | `geometric_convergence` | dist(fⁿ(x), x*) ≤ cⁿ/(1-c) · dist(x, f(x)) |
| 4 | `tendsto_iterate_fixedPoint` | Iterates converge: fⁿ(x) → x* |

### Layer 2 — Composition rules

| # | Name | Statement |
|---|------|-----------|
| 5 | `IsContracting.comp` | c₁-contracting ∘ c₂-contracting = (c₁·c₂)-contracting |
| 6 | `IsContracting.iterate` | n-th iterate of c-contracting is cⁿ-contracting |

### Layer 3 — Differential contraction (Lohmiller-Slotine)

| # | Name | Statement |
|---|------|-----------|
| 7 | `IsContracting.of_deriv_le` | ‖f'(x)‖ ≤ c < 1 implies f is c-contracting (via MVT) |
| 8 | `exponential_decay_of_deriv_le` | u'(t) ≤ -μ·u(t) implies u(t) ≤ u(0)·e^(-μt) (Gronwall) |
| 9 | `trajectory_convergence` | ‖x₁(t) - x₂(t)‖ ≤ e^(-μt)·‖x₁(0) - x₂(0)‖ under contraction differential inequality |

## Key technical highlights

- `IsContracting` wraps Mathlib's `ContractingWith` for a clean API while reusing its infrastructure
- `geometric_convergence` gives explicit rate, not just fixed-point existence
- `exponential_decay_of_deriv_le` proved via antitone auxiliary v(t) = u(t)·e^(μt), using `antitoneOn_of_deriv_nonpos`
- `of_deriv_le` uses `lipschitzWith_of_nnnorm_deriv_le` (MVT-based Lipschitz bound)
- Standard axioms only: `propext`, `Classical.choice`, `Quot.sound`
- Zero `sorry`, zero `admit`

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

**contraction-lean: Formal Proofs of Contraction Theory, Banach Fixed Point, and Exponential Convergence in Lean 4**  
Ben Cassie (2026). Zenodo.  
https://zenodo.org/records/20474762

## Cite

Cassie, B. (2026). *contraction-lean: Formal Proofs of Contraction Theory, Banach Fixed Point, and Exponential Convergence in Lean 4*. Zenodo. https://zenodo.org/records/20474762.

## Related work

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) — Lean 4 Kuramoto synchronisation (contraction results in Contraction.lean)
- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence
- [hopfield-lean](https://github.com/velvetmonkey/hopfield-lean) — Lean 4 Hopfield attractor convergence
- [nesterov-lean](https://github.com/velvetmonkey/nesterov-lean) — Lean 4 Nesterov accelerated gradient descent
- [lotka-volterra-lean](https://github.com/velvetmonkey/lotka-volterra-lean) — Lean 4 Lotka-Volterra Hamiltonian conservation

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline -- zero sorry, every Mathlib lemma name `#check`ed before use -- was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).

## Moving fixed point

The root module re-exports `ContractionLean.MovingFixedPoint`, which studies maps `T n` that change at every step,
fixed points `xs n` of those maps, and an orbit satisfying
`z (n+1) = T n (z n)`. Write `e n = dist (z n) (xs n)`. The common Lipschitz
constant `K` is a nonnegative real (`ℝ≥0` in Lean); drift bounds are real numbers.

- `MovingFixedPoint.tracking_step`: in a metric space, if every `T n` is
  `K`-Lipschitz, each `xs n` is its fixed point, and successive fixed points
  have distance at most `δ`, then `e (n+1) ≤ K * e n + δ`.
- `MovingFixedPoint.tracking_bound`: under the same assumptions and `K < 1`,
  `e n ≤ K^n * e 0 + δ / (1-K)` for every natural number `n`.
- `MovingFixedPoint.tracking_eventually`: under those assumptions, for every
  `ε > 0`, eventually `e n ≤ δ / (1-K) + ε`. These three results require no
  completeness assumption because the fixed points are supplied.
- `MovingFixedPoint.fixedPoint_drift_of_map_drift`: if every map is
  `ContractingWith K`, the fixed points are supplied, and
  `dist (T (n+1) x) (T n x) ≤ C` for every `n` and `x`, then successive fixed
  points have distance at most `C / (1-K)`. This uses Mathlib's
  `ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'`.
- `MovingFixedPoint.tracking_bound_of_map_drift`: on a nonempty complete metric
  space, with the same contraction and uniform map-drift hypotheses and the
  orbit recurrence, the error relative to the canonical fixed points is at most
  `K^n * e 0 + C / (1-K)^2`. The fixed-point drift is obtained from Mathlib's
  `ContractingWith.fixedPoint_lipschitz_in_map`.
- `MovingFixedPoint.identity_tracking_unbounded`: for any `δ > 0`, identity maps
  on the real numbers are `1`-Lipschitz and fix `xs n = n * δ`, whose drift is
  `δ`. The constant orbit `z n = 0` has error exceeding every fixed real bound
  `B` at some natural number `n`. Thus strict contraction cannot be dropped
  from the uniform or eventual result. Its one-step error also exceeds the
  zero-drift estimate, showing that the drift hypothesis in `tracking_step`
  matters. A checked zero-drift example shows why this negative control needs
  `δ > 0`.
