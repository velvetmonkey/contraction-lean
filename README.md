# contraction-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ContractionLean)

Lean 4 formal proofs of contraction theory: Banach fixed point theorem, geometric convergence rates, composition rules, and Lohmiller-Slotine differential contraction.

**Zero sorry statements.** Zero new axioms.

## Why it matters

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

Companion paper forthcoming. To be published on Zenodo.

## Cite

Zenodo DOI forthcoming.

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
