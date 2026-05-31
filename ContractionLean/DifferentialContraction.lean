/-
Copyright (c) 2025 Contraction-Lean Library. All rights reserved.
Released under Apache 2.0 license.

# ContractionLean.DifferentialContraction

Differential criteria for contraction: derivative bounds and ODE trajectory convergence.
-/
import ContractionLean.Defs

/-!
# Differential Contraction

## Main results

### Derivative bound implies contraction (Theorem 4)

* `IsContracting.of_deriv_le` — If `f : ℝ → ℝ` is differentiable and `‖f'(x)‖ ≤ c` for
  some `c < 1`, then `f` is `c`-contracting.

### ODE trajectory convergence (Theorem 5 — Lohmiller–Slotine)

* `exponential_decay_of_deriv_le` — A scalar Gronwall-type decay lemma: if a nonneg
  differentiable function `u` satisfies `u'(t) ≤ -μ · u(t)` on `[0, T]`, then
  `u(t) ≤ u(0) · e^{-μ t}`.
* `trajectory_convergence` — If two continuous trajectories `x₁, x₂ : ℝ → E` have
  a distance function `t ↦ ‖x₁(t) - x₂(t)‖` satisfying the contraction differential
  inequality (as implied by `½(J + Jᵀ) ≼ -μI`), then
  `‖x₁(t) - x₂(t)‖ ≤ e^{-μt} · ‖x₁(0) - x₂(0)‖`.

The passage from the Jacobian symmetry condition to the differential inequality on
the norm is the content of the Lohmiller–Slotine theorem; the exponential decay
then follows from the Gronwall bound formalized here.
-/

open NNReal ENNReal Topology Filter Function Set Real

/-! ## Part 1: Derivative bound implies contraction -/

/-- If `f : ℝ → ℝ` is differentiable everywhere and `‖f'(x)‖ ≤ c` for some `c < 1`,
then `f` is `c`-contracting. Uses the mean value theorem. -/
theorem IsContracting.of_deriv_le {c : ℝ≥0} (hc : c < 1) {f : ℝ → ℝ}
    (hf_diff : Differentiable ℝ f)
    (hf_bound : ∀ x : ℝ, ‖deriv f x‖ ≤ c) :
    IsContracting c f :=
  IsContracting.mk' hc (lipschitzWith_of_nnnorm_deriv_le hf_diff hf_bound)

/-! ## Part 2: Exponential decay (Gronwall-type) -/

/-- **Gronwall decay lemma**: if `u : ℝ → ℝ` is continuous on `[0, T]`,
differentiable on `(0, T)`, nonneg, and satisfies `u'(t) ≤ -μ · u(t)` for all
`t ∈ (0, T)` with `μ > 0`, then `u(t) ≤ u(0) · e^{-μ t}` for all `t ∈ [0, T]`. -/
theorem exponential_decay_of_deriv_le
    {u : ℝ → ℝ} {T mu : ℝ} (_hmu : 0 < mu) (hT : 0 ≤ T)
    (hu_cont : ContinuousOn u (Icc 0 T))
    (hu_diff : DifferentiableOn ℝ u (interior (Icc 0 T)))
    (_hu_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ u t)
    (hu_deriv : ∀ t ∈ interior (Icc 0 T), deriv u t ≤ -mu * u t) :
    ∀ t ∈ Icc 0 T, u t ≤ u 0 * exp (-mu * t) := by
  -- Define v(t) = u(t) · exp(mu · t). Show v is antitone, hence v(t) ≤ v(0) = u(0).
  have hv_deriv_nonpos :
      ∀ t ∈ Set.Ioo 0 T, deriv (fun t => u t * Real.exp (mu * t)) t ≤ 0 := by
    intro t ht; convert HasDerivAt.deriv ( HasDerivAt.mul ( hu_diff.hasDerivAt ( Filter.mem_of_superset ( Ioo_mem_nhds ht.1 ht.2 ) fun x hx => ?_ ) ) ( HasDerivAt.exp ( HasDerivAt.const_mul mu ( hasDerivAt_id t ) ) ) ) |> fun v => v.le.trans ?_ using 1 ; ring_nf ; aesop;
    nlinarith! [ hu_deriv t ( by simpa [ hT ] using ht ), Real.exp_pos ( mu * t ) ];
  have hv_antitone : AntitoneOn (fun t => u t * Real.exp (mu * t)) (Set.Icc 0 T) := by
    apply_rules [antitoneOn_of_deriv_nonpos]
    · exact convex_Icc _ _
    · fun_prop
    · exact hu_diff.mul (DifferentiableOn.exp (differentiableOn_id.const_mul mu))
    · aesop
  intro t ht; specialize hv_antitone ( show 0 ∈ Set.Icc 0 T by norm_num; linarith ) ( show t ∈ Set.Icc 0 T by assumption ) ht.1; simp_all +decide [ Real.exp_neg ] ;
  rwa [ ← div_eq_mul_inv, le_div_iff₀ ( Real.exp_pos _ ) ]

/-! ## Part 3: Trajectory convergence (Lohmiller–Slotine consequence) -/

/-- **ODE contraction / Lohmiller–Slotine consequence**: If `x₁` and `x₂` are continuous
trajectories on `[0, T]` in a normed space, and the distance function
`δ(t) = ‖x₁(t) - x₂(t)‖` is differentiable with `δ'(t) ≤ -μ · δ(t)` (as implied
by the symmetric-Jacobian condition `½(J + Jᵀ) ≼ -μI`), then
`‖x₁(t) - x₂(t)‖ ≤ e^{-μt} · ‖x₁(0) - x₂(0)‖`. -/
theorem trajectory_convergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x₁ x₂ : ℝ → E} {T mu : ℝ} (hmu : 0 < mu) (hT : 0 ≤ T)
    (hx₁ : ContinuousOn x₁ (Icc 0 T))
    (hx₂ : ContinuousOn x₂ (Icc 0 T))
    (hdelta_diff : DifferentiableOn ℝ (fun t => ‖x₁ t - x₂ t‖) (interior (Icc 0 T)))
    (hdelta_deriv : ∀ t ∈ interior (Icc 0 T),
      deriv (fun t => ‖x₁ t - x₂ t‖) t ≤ -mu * ‖x₁ t - x₂ t‖) :
    ∀ t ∈ Icc 0 T, ‖x₁ t - x₂ t‖ ≤ exp (-mu * t) * ‖x₁ 0 - x₂ 0‖ := by
  have h := exponential_decay_of_deriv_le hmu hT
    (ContinuousOn.norm (hx₁.sub hx₂)) hdelta_diff (fun t _ => norm_nonneg _) hdelta_deriv
  simpa only [mul_comm] using h
