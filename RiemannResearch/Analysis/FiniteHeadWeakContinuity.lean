import RiemannResearch.Analysis.NormalizedProjectionWeakConvergence

/-!
# Finite-head operator approximations send bounded weak-zero vectors to zero

Source: standard finite-rank approximation argument, specialized to the
reciprocal-coordinate multiplier in the exact optimizer cancellation program.
The finite-head representations and the operator-norm tail estimate are kept
explicit. Thus the reciprocal multiplier can be instantiated directly, without
an abstract compact-operator spectral theorem or an assumed RH implication.

All finite heads retain their complete signed sums. The final norm estimate
uses the complete finite head plus the operator-norm remainder.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.FiniteHeadWeakContinuity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Strong zero limits for every finite head and a vanishing uniform operator
tail give the strong zero limit of the complete operator image. -/
theorem image_tendsto_zero_of_finiteHeadApproximation
    (D : H →L[ℝ] H) (F : ℕ → H →L[ℝ] H) (u : ℕ → H) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ᶠ n in atTop, ‖u n‖ ≤ C)
    (htail : Tendsto (fun j => ‖D - F j‖) atTop (𝓝 0))
    (hhead : ∀ j, Tendsto (fun n => F j (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => D (u n)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hsmall : (0 : ℝ) < δ / (2 * (C + 1)) := by positivity
  obtain ⟨j, hj⟩ := (htail.eventually_lt_const hsmall).exists
  have hh : Tendsto (fun n => ‖F j (u n)‖) atTop (𝓝 0) := by
    simpa using (hhead j).norm
  filter_upwards [hbound, hh.eventually_lt_const (half_pos hδ)] with n hn hhn
  have hmul : ‖D - F j‖ * (2 * (C + 1)) < δ :=
    (lt_div_iff₀ (by positivity)).mp hj
  have htailSmall : ‖D - F j‖ * C < δ / 2 := by
    nlinarith [norm_nonneg (D - F j)]
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  calc
    ‖D (u n)‖ = ‖(D - F j) (u n) + F j (u n)‖ := by simp
    _ ≤ ‖(D - F j) (u n)‖ + ‖F j (u n)‖ := norm_add_le _ _
    _ ≤ ‖D - F j‖ * C + ‖F j (u n)‖ := by
      exact add_le_add
        (((D - F j).le_opNorm (u n)).trans
          (mul_le_mul_of_nonneg_left hn (norm_nonneg (D - F j)))) le_rfl
    _ < δ := by linarith

/-- Every explicit finite-rank head tends strongly to zero along a weak-zero
sequence. The weak tests are the literal finite coefficient pairings. -/
theorem finiteHead_image_tendsto_zero
    (T : H →L[ℝ] H) (u : ℕ → H)
    (hweak : ∀ y : H, Tendsto (fun n => inner ℝ y (u n)) atTop (𝓝 0))
    (m : ℕ) (a b : Fin m → H)
    (hT : ∀ x, T x = ∑ i : Fin m, inner ℝ (a i) x • b i) :
    Tendsto (fun n => T (u n)) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ
    (fun i _ => (hweak (a i)).smul (tendsto_const_nhds (x := b i)))
  simpa only [hT, zero_smul, Finset.sum_const_zero] using hsum

/-- An operator-norm limit of explicit finite pairing heads is weak-to-strong
continuous on bounded sequences. -/
theorem image_tendsto_zero_of_bounded_weakZero
    (D : H →L[ℝ] H) (F : ℕ → H →L[ℝ] H) (u : ℕ → H) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ᶠ n in atTop, ‖u n‖ ≤ C)
    (hweak : ∀ y : H, Tendsto (fun n => inner ℝ y (u n)) atTop (𝓝 0))
    (htail : Tendsto (fun j => ‖D - F j‖) atTop (𝓝 0))
    (hfinite : ∀ j, ∃ m : ℕ, ∃ a b : Fin m → H,
      ∀ x, F j x = ∑ i : Fin m, inner ℝ (a i) x • b i) :
    Tendsto (fun n => D (u n)) atTop (𝓝 0) := by
  apply image_tendsto_zero_of_finiteHeadApproximation D F u C hC hbound htail
  intro j
  obtain ⟨m, a, b, hF⟩ := hfinite j
  exact finiteHead_image_tendsto_zero (F j) u hweak m a b hF

open RiemannResearch.Analysis.NormalizedProjectionWeakConvergence

/-- Exact relationship between the normalized-vector image and the normalized
weighted energy, including Lean's zero-division convention. -/
theorem normalizedResidual_image_norm_sq (D : H →L[ℝ] H) (r : H) :
    ‖D (normalizedResidual r)‖ ^ 2 = ‖D r‖ ^ 2 / ‖r‖ ^ 2 := by
  rw [normalizedResidual, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg r), mul_pow, inv_pow, div_eq_mul_inv, mul_comm]

variable [CompleteSpace H]
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The zero-limit compact-ratio provider for canonical cumulative projections
is discharged by finite-head approximation and proved weak-zero geometry. -/
theorem normalizedWalkResidual_image_energy_ratio_tendsto_zero
    (v : ℕ → H) (x : H) (D : H →L[ℝ] H) (F : ℕ → H →L[ℝ] H)
    (hr : Tendsto (fun n => x - (walkSpan v id n).starProjection x) atTop (𝓝 0))
    (hne : ∀ n, x - (walkSpan v id n).starProjection x ≠ 0)
    (htail : Tendsto (fun j => ‖D - F j‖) atTop (𝓝 0))
    (hfinite : ∀ j, ∃ m : ℕ, ∃ a b : Fin m → H,
      ∀ y, F j y = ∑ i : Fin m, inner ℝ (a i) y • b i) :
    Tendsto (fun n =>
      ‖D (x - (walkSpan v id n).starProjection x)‖ ^ 2 /
        ‖x - (walkSpan v id n).starProjection x‖ ^ 2) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,
      ‖normalizedResidual (x - (walkSpan v id n).starProjection x)‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro n
    rw [normalizedResidual_norm_eq_one _ (hne n)]
  have himage := image_tendsto_zero_of_bounded_weakZero D F
    (fun n => normalizedResidual (x - (walkSpan v id n).starProjection x)) 1
    (by norm_num) hbound
    (fun y => normalizedWalkResidual_inner_tendsto_zero v x hr hne y) htail hfinite
  simpa only [normalizedResidual_image_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    using himage.norm.pow 2

end RiemannResearch.Analysis.FiniteHeadWeakContinuity
