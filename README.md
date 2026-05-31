# contraction-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-pending-lightgrey)](Contraction)

Lean 4 formal proofs of contraction theory: Banach fixed point theorem, geometric convergence rates, composition rules, and differential contraction.

**Zero sorry statements.**

## Why it matters

Contraction theory (Lohmiller and Slotine, 1998) provides a unified framework for proving exponential convergence of nonlinear dynamical systems. A contracting system forgets its initial conditions at an exponential rate -- any two trajectories converge toward each other regardless of where they started. This is a stronger and more composable property than Lyapunov stability.

Contraction theory underlies distributed synchronisation, neural dynamics, reinforcement learning, and control theory. This library machine-checks the core results: Banach fixed point with explicit rates, composition rules for building contracting systems, and the differential (Jacobian) condition for ODEs.

## Planned project structure

```
Contraction/
├── Defs.lean                    — Contracting maps, contraction constant, metric setting
├── BanachFixed.lean             — Unique fixed point + geometric convergence rate
├── CompositionRules.lean        — Series, parallel, feedback combinations
└── DifferentialContraction.lean — Jacobian condition for ODE systems
```

## Planned theorem inventory

### Layer 1 — Metric contraction

| # | Theorem | Statement |
|---|---------|-----------|
| 1 | `contracting_map_def` | d(f(x), f(y)) ≤ c * d(x, y) for c ∈ [0,1) |
| 2 | `banach_fixed_point` | Unique fixed point x* exists |
| 3 | `geometric_convergence` | d(fⁿ(x), x*) ≤ cⁿ/(1-c) * d(f(x), x) |
| 4 | `composition_contracting` | c₁-contracting ∘ c₂-contracting is (c₁*c₂)-contracting |

### Layer 2 — Smooth contraction

| # | Theorem | Statement |
|---|---------|-----------|
| 5 | `smooth_contraction_of_deriv` | \|f'(x)\| ≤ c < 1 implies f is c-contracting |
| 6 | `differential_contraction` | Symmetric Jacobian ½(J + Jᵀ) ≼ -λI implies ‖x₁(t)-x₂(t)‖ ≤ e^(-λt)‖x₁(0)-x₂(0)‖ |

## Key technical highlights

- Explicit geometric convergence rate, not just existence
- Composition rules make contraction theory modular: build large contracting systems from small ones
- Differential contraction bridges algebraic (Jacobian) condition to trajectory behaviour
- Standard axioms only: `propext`, `Classical.choice`, `Quot.sound`
- Zero `sorry`, zero `admit`

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

Companion paper forthcoming. To be published on Zenodo.

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
