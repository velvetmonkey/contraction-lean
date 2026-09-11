import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Tracking a moving fixed point

The maps may change at every step. The Lipschitz constant is nonnegative by type;
drift and distance bounds are real numbers. No completeness is needed when the
fixed points are supplied. The map-drift corollaries reuse Mathlib's
`ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'` and
`ContractingWith.fixedPoint_lipschitz_in_map`.
-/

open Filter Topology Function

namespace MovingFixedPoint

variable {α : Type*} [MetricSpace α] {K : NNReal}
  {T : ℕ → α → α} {xs z : ℕ → α} {δ : ℝ}

/-- One step of tracking needs a Lipschitz map and a bound on fixed-point drift.
Strict contraction is needed only for the uniform and eventual bounds. -/
theorem tracking_step
    (hT : ∀ n, LipschitzWith K (T n))
    (hxs : ∀ n, IsFixedPt (T n) (xs n))
    (hδ : ∀ n, dist (xs (n + 1)) (xs n) ≤ δ)
    (hz : ∀ n, z (n + 1) = T n (z n)) (n : ℕ) :
    dist (z (n + 1)) (xs (n + 1)) ≤ (K : ℝ) * dist (z n) (xs n) + δ := by
  calc
    dist (z (n + 1)) (xs (n + 1)) ≤
        dist (z (n + 1)) (xs n) + dist (xs n) (xs (n + 1)) :=
      dist_triangle _ _ _
    _ ≤ (K : ℝ) * dist (z n) (xs n) + δ := by
      apply add_le_add
      · simpa only [hz n, (hxs n).eq] using (hT n).dist_le_mul (z n) (xs n)
      · simpa only [dist_comm] using hδ n

/-- Geometric decay of the initial error plus the uniform drift allowance. -/
theorem tracking_bound (hK : K < 1)
    (hT : ∀ n, LipschitzWith K (T n))
    (hxs : ∀ n, IsFixedPt (T n) (xs n))
    (hδ : ∀ n, dist (xs (n + 1)) (xs n) ≤ δ)
    (hz : ∀ n, z (n + 1) = T n (z n)) (n : ℕ) :
    dist (z n) (xs n) ≤ (K : ℝ) ^ n * dist (z 0) (xs 0) + δ / (1 - K) := by
  have hpos : (0 : ℝ) < 1 - K := sub_pos.mpr (NNReal.coe_lt_one.mpr hK)
  have hδ0 : 0 ≤ δ := (dist_nonneg.trans (hδ 0))
  have hid : (K : ℝ) * (δ / (1 - K)) + δ = δ / (1 - K) := by
    field_simp [ne_of_gt hpos]
    ring
  induction n with
  | zero => simpa using div_nonneg hδ0 hpos.le
  | succ n ih =>
    calc
      dist (z (n + 1)) (xs (n + 1)) ≤ (K : ℝ) * dist (z n) (xs n) + δ :=
        tracking_step hT hxs hδ hz n
      _ ≤ (K : ℝ) * ((K : ℝ) ^ n * dist (z 0) (xs 0) + δ / (1 - K)) + δ :=
        add_le_add (mul_le_mul_of_nonneg_left ih K.coe_nonneg) le_rfl
      _ = (K : ℝ) ^ (n + 1) * dist (z 0) (xs 0) + δ / (1 - K) := by
        rw [mul_add, add_assoc, hid, pow_succ]
        ring

/-- Eventually the error is within any positive tolerance of the drift allowance. -/
theorem tracking_eventually (hK : K < 1)
    (hT : ∀ n, LipschitzWith K (T n))
    (hxs : ∀ n, IsFixedPt (T n) (xs n))
    (hδ : ∀ n, dist (xs (n + 1)) (xs n) ≤ δ)
    (hz : ∀ n, z (n + 1) = T n (z n)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, dist (z n) (xs n) ≤ δ / (1 - K) + ε := by
  have ht : Tendsto (fun n : ℕ => (K : ℝ) ^ n * dist (z 0) (xs 0)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
      (NNReal.coe_lt_one.mpr hK)).mul_const (dist (z 0) (xs 0))
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  have hb := tracking_bound hK hT hxs hδ hz n
  linarith

/-- Uniform map drift gives drift of any supplied fixed points; completeness is unnecessary. -/
theorem fixedPoint_drift_of_map_drift
    (hT : ∀ n, ContractingWith K (T n))
    (hxs : ∀ n, IsFixedPt (T n) (xs n)) {C : ℝ}
    (hC : ∀ n x, dist (T (n + 1) x) (T n x) ≤ C) (n : ℕ) :
    dist (xs (n + 1)) (xs n) ≤ C / (1 - K) := by
  exact (hT (n + 1)).dist_fixedPoint_fixedPoint_of_dist_le' (T n)
    (hxs (n + 1)) (hxs n) (hC n)

/-- On a nonempty complete metric space, map drift yields a squared-denominator
tracking allowance for the canonical fixed points. -/
theorem tracking_bound_of_map_drift [CompleteSpace α] [Nonempty α]
    (hT : ∀ n, ContractingWith K (T n)) {C : ℝ}
    (hC : ∀ n x, dist (T (n + 1) x) (T n x) ≤ C)
    (hz : ∀ n, z (n + 1) = T n (z n)) (n : ℕ) :
    dist (z n) ((hT n).fixedPoint (T n)) ≤
      (K : ℝ) ^ n * dist (z 0) ((hT 0).fixedPoint (T 0)) + C / (1 - K) ^ 2 := by
  have hd : ∀ n, dist ((hT (n + 1)).fixedPoint (T (n + 1)))
      ((hT n).fixedPoint (T n)) ≤ C / (1 - K) := fun n =>
    (hT (n + 1)).fixedPoint_lipschitz_in_map (hT n) (hC n)
  have hb := tracking_bound (hT 0).1 (fun n => (hT n).toLipschitzWith)
    (fun n => (hT n).fixedPoint_isFixedPt) hd hz n
  simpa only [div_div, pow_two] using hb

/-- At K = 1, identity maps admit a linearly drifting fixed-point sequence and a
constant orbit whose error exceeds every constant. The last conjunct also
refutes the one-step estimate if the drift hypothesis is omitted (allowance 0). -/
theorem identity_tracking_unbounded (δ : ℝ) (hδ : 0 < δ) :
    (∀ _n : ℕ, LipschitzWith 1 (fun x : ℝ => x)) ∧
    (∀ n : ℕ, IsFixedPt (fun x : ℝ => x) ((n : ℝ) * δ)) ∧
    (∀ n : ℕ, dist (((n + 1 : ℕ) : ℝ) * δ) ((n : ℝ) * δ) ≤ δ) ∧
    (∀ _n : ℕ, (0 : ℝ) = (fun x : ℝ => x) 0) ∧
    (∀ B : ℝ, ∃ n : ℕ, B < dist (0 : ℝ) ((n : ℝ) * δ)) ∧
    ¬ (dist (0 : ℝ) ((1 : ℝ) * δ) ≤ 1 * dist (0 : ℝ) ((0 : ℝ) * δ) + 0) := by
  refine ⟨fun _ => LipschitzWith.id, fun _ => rfl, ?_, fun _ => rfl, ?_, ?_⟩
  · intro n
    rw [Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have he : ((n : ℝ) + 1) * δ - (n : ℝ) * δ = δ := by ring
    rw [he, abs_of_pos hδ]
  · intro B
    obtain ⟨n, hn⟩ := exists_nat_gt (B / δ)
    refine ⟨n, ?_⟩
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hδ.le)]
    exact (div_lt_iff₀ hδ).mp hn
  · simpa [Real.dist_eq, abs_of_pos hδ] using (not_le.mpr hδ)

-- Checked necessity of the negative control's positive-drift hypothesis:
-- at δ = 0 the claimed unboundedness is false.
#check (show ¬ (∀ B : ℝ, ∃ n : ℕ, B < dist (0 : ℝ) ((n : ℝ) * 0)) from by
  intro h
  obtain ⟨n, hn⟩ := h 0
  simp at hn)

#print axioms tracking_step
#print axioms tracking_bound
#print axioms tracking_eventually
#print axioms fixedPoint_drift_of_map_drift
#print axioms tracking_bound_of_map_drift
#print axioms identity_tracking_unbounded

end MovingFixedPoint
