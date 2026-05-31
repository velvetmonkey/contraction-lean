/-
Copyright (c) 2025 Contraction-Lean Library. All rights reserved.
Released under Apache 2.0 license.

# ContractionLean.CompositionRules

Composition and iteration rules for contracting maps.
-/
import ContractionLean.Defs

/-!
# Composition Rules for Contracting Maps

## Main results

* `IsContracting.comp` — composition of a `c₁`-contracting and a `c₂`-contracting map
  is `(c₁ * c₂)`-contracting.
* `IsContracting.iterate` — the `n`-th iterate (`n ≥ 1`) of a `c`-contracting map is
  `c ^ n`-contracting.
-/

open NNReal ENNReal Topology Filter Function

namespace IsContracting

variable {α : Type*} [EMetricSpace α]

/-- Composition of contracting maps: if `f` is `c₁`-contracting and `g` is `c₂`-contracting,
then `f ∘ g` is `(c₁ * c₂)`-contracting. -/
theorem comp {c₁ c₂ : ℝ≥0} {f g : α → α}
    (hf : IsContracting c₁ f) (hg : IsContracting c₂ g) :
    IsContracting (c₁ * c₂) (f ∘ g) := by
  exact IsContracting.mk'
    (mul_lt_one_of_nonneg_of_lt_one_left (zero_le _) hf.const_lt_one hg.const_lt_one.le)
    (hf.lipschitz.comp hg.lipschitz)

/-- The `n`-th iterate (`n ≥ 1`) of a `c`-contracting map is `c ^ n`-contracting. -/
theorem iterate {c : ℝ≥0} {f : α → α}
    (hf : IsContracting c f) {n : ℕ} (hn : 0 < n) :
    IsContracting (c ^ n) (f^[n]) :=
  IsContracting.mk'
    (pow_lt_one₀ (zero_le _) hf.const_lt_one hn.ne')
    (hf.lipschitz.iterate n)

end IsContracting
