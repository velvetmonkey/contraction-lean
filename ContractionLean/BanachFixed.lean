/-
Copyright (c) 2025 Contraction-Lean Library. All rights reserved.
Released under Apache 2.0 license.

# ContractionLean.BanachFixed

Banach fixed-point theorem and geometric convergence estimates.
-/
import ContractionLean.Defs

/-!
# Banach Fixed-Point Theorem & Geometric Convergence

## Main results

* `IsContracting.exists_unique_fixedPoint` — existence and uniqueness of the fixed point
* `IsContracting.fixedPoint` — the (noncomputable) fixed point
* `IsContracting.fixedPoint_isFixedPt` — the fixed point is indeed fixed
* `IsContracting.fixedPoint_unique` — uniqueness
* `IsContracting.geometric_convergence` — d(fⁿ(x), x*) ≤ cⁿ/(1-c) · d(f(x), x)
-/

open NNReal ENNReal Topology Filter Function

namespace IsContracting

variable {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
  {c : ℝ≥0} {f : α → α}

/-! ### Fixed point existence and uniqueness -/

/-- The unique fixed point of a contracting map on a nonempty complete metric space. -/
noncomputable def fixedPoint (hf : IsContracting c f) : α :=
  hf.toContractingWith.fixedPoint f

/-- The fixed point is a fixed point. -/
theorem fixedPoint_isFixedPt (hf : IsContracting c f) :
    IsFixedPt f (fixedPoint hf) :=
  hf.toContractingWith.fixedPoint_isFixedPt

/-- `f(x*) = x*` -/
theorem fixedPoint_eq (hf : IsContracting c f) :
    f (fixedPoint hf) = fixedPoint hf :=
  hf.fixedPoint_isFixedPt

/-- The fixed point is unique: any other fixed point equals `fixedPoint`. -/
theorem fixedPoint_unique (hf : IsContracting c f) {y : α}
    (hy : IsFixedPt f y) : y = fixedPoint hf :=
  hf.toContractingWith.fixedPoint_unique hy

/-- Existence and uniqueness of the fixed point, packaged as `∃!`. -/
theorem exists_unique_fixedPoint (hf : IsContracting c f) :
    ∃! x : α, f x = x :=
  ⟨fixedPoint hf, fixedPoint_eq hf,
    fun _ hy => (fixedPoint_unique hf hy)⟩

/-- Iterates converge to the fixed point. -/
theorem tendsto_iterate_fixedPoint (hf : IsContracting c f) (x : α) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 (fixedPoint hf)) :=
  hf.toContractingWith.tendsto_iterate_fixedPoint x

/-! ### Geometric convergence -/

/-
A priori geometric convergence rate:
`dist(fⁿ(x), x*) ≤ c ^ n / (1 - c) * dist(x, f(x))`.
-/
theorem geometric_convergence (hf : IsContracting c f) (x : α) (n : ℕ) :
    dist (f^[n] x) (fixedPoint hf) ≤
      (c : ℝ) ^ n / (1 - (c : ℝ)) * dist x (f x) := by
  convert hf.toContractingWith.apriori_dist_iterate_fixedPoint_le x n using 1;
  ring

/-- The distance from any point to the fixed point is bounded by
`dist(x, f(x)) / (1 - c)`. -/
theorem dist_fixedPoint_le (hf : IsContracting c f) (x : α) :
    dist x (fixedPoint hf) ≤ dist x (f x) / (1 - (c : ℝ)) :=
  hf.toContractingWith.dist_fixedPoint_le x

end IsContracting