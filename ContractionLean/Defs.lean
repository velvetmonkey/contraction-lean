/-
Copyright (c) 2025 Contraction-Lean Library. All rights reserved.
Released under Apache 2.0 license.

# ContractionLean.Defs

Core definitions for contraction mapping theory, built on top of Mathlib's
`ContractingWith` and `LipschitzWith` infrastructure.
-/
import Mathlib

/-!
# Definitions for Contraction Mapping Theory

We define `IsContracting` as a bundled predicate packaging a contraction constant
`c ∈ [0, 1)` together with the Lipschitz condition `d(f(x), f(y)) ≤ c * d(x, y)`.

## Main definitions

* `IsContracting c f` — `f` is `c`-contracting (synonym for `ContractingWith c f`)
* Basic API: extraction of the Lipschitz constant, the contraction bound, etc.
-/

open NNReal ENNReal Topology Filter Function

/-- A self-map `f : α → α` on an emetric space is *c-contracting* if `c < 1`
and `f` is Lipschitz with constant `c`. This is definitionally equal to
Mathlib's `ContractingWith`. -/
def IsContracting {α : Type*} [EMetricSpace α] (c : ℝ≥0) (f : α → α) : Prop :=
  ContractingWith c f

namespace IsContracting

variable {α : Type*} [EMetricSpace α] {c : ℝ≥0} {f : α → α}

/-- An `IsContracting` map has contraction constant strictly less than 1. -/
theorem const_lt_one (hf : IsContracting c f) : c < 1 := hf.1

/-- An `IsContracting` map is Lipschitz with constant `c`. -/
theorem lipschitz (hf : IsContracting c f) : LipschitzWith c f := hf.2

/-- Convert `IsContracting` to Mathlib's `ContractingWith`. -/
theorem toContractingWith (hf : IsContracting c f) : ContractingWith c f := hf

/-- Convert Mathlib's `ContractingWith` to `IsContracting`. -/
theorem ofContractingWith (hf : ContractingWith c f) : IsContracting c f := hf

/-- The contraction bound on extended distances. -/
theorem edist_le (hf : IsContracting c f) (x y : α) :
    edist (f x) (f y) ≤ c * edist x y :=
  hf.lipschitz x y

/-- An `IsContracting` map is continuous. -/
theorem continuous (hf : IsContracting c f) : Continuous f :=
  hf.lipschitz.continuous

/-- Build `IsContracting` from `c < 1` and the Lipschitz condition. -/
theorem mk' (hc : c < 1) (hL : LipschitzWith c f) : IsContracting c f :=
  ⟨hc, hL⟩

section MetricSpace

variable {β : Type*} [MetricSpace β] {c : ℝ≥0} {g : β → β}

/-- The contraction bound on distances (in a metric space). -/
theorem dist_le (hg : IsContracting c g) (x y : β) :
    dist (g x) (g y) ≤ c * dist x y :=
  hg.toContractingWith.dist_le_mul x y

/-- `1 - c > 0` as a real number. -/
theorem one_sub_c_pos (hg : IsContracting c g) : (0 : ℝ) < 1 - c :=
  hg.toContractingWith.one_sub_K_pos

end MetricSpace

end IsContracting
