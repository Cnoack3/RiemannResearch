/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.VectorKronecker

/-!
# Joint Abel convergence with increasing triangular weights

For a convergent signed vector series, increasing nonnegative weights may
vary with the cutoff provided their terminal values remain bounded and
each fixed coefficient tends to one.  The finite Abel identity controls
the signed tail by twice the terminal weight.  No absolute summability
of the original series is assumed.

The quantitative extension retains the complete centered prefix-error
budget and permits unbounded terminal weights when that budget vanishes.
`IncreasingLogWeights` supplies its scalar power/log-profile estimate.

This is a direct finite Abel regularity argument, with no novelty claim.
Its arithmetic consumer is an unconditional shrinking band below the
half-damping endpoint of the Möbius residue series.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Increasing triangular weights preserve a natural-order vector limit
when their terminal values have a common bound and each fixed weight
tends to one. All norms are taken after the complete signed sums. -/
theorem signedVector_increasing_weights_joint_tendsto
    (u : ℕ → E) {f : E} (hf : Tendsto (signedVectorPrefix u) atTop (𝓝 f))
    (w : ℕ → ℕ → ℝ) (hw : ∀ j, Monotone (w j))
    (hwn : ∀ j n, 0 ≤ w j n)
    (hlim : ∀ n, Tendsto (fun j => w j n) atTop (𝓝 1))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {B : ℝ} (hB : 0 < B) (hterminal : ∀ j, w j (M j) ≤ B) :
    Tendsto (fun j => ∑ n ∈ Finset.range (M j), w j n • u n) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hf (η / (8 * (B + 1))) (by positivity)
  have hKf : ‖signedVectorPrefix u K - f‖ < η / (8 * (B + 1)) := by
    simpa only [dist_eq_norm] using hK K le_rfl
  have htail (n : ℕ) :
      ‖signedVectorPrefix u (K + n) - signedVectorPrefix u K‖ ≤ η / (4 * (B + 1)) := by
    have hn : ‖signedVectorPrefix u (K + n) - f‖ < η / (8 * (B + 1)) := by
      simpa only [dist_eq_norm] using hK (K + n) (by omega)
    have ht := dist_triangle (signedVectorPrefix u (K + n)) f (signedVectorPrefix u K)
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev f] at ht
    have hfrac : η / (4 * (B + 1)) = 2 * (η / (8 * (B + 1))) := by
      field_simp [ne_of_gt (show 0 < B + 1 by linarith)]
      ring
    rw [hfrac]
    linarith
  have hhead : Tendsto (fun j => ∑ n ∈ Finset.range K, w j n • u n)
      atTop (𝓝 (signedVectorPrefix u K)) := by
    simpa only [one_smul, signedVectorPrefix] using
      tendsto_finsetSum (Finset.range K) (fun n _ => (hlim n).smul_const (u n))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hhead (η / 4) (by positivity)
  obtain ⟨J', hJ'⟩ := eventually_atTop.mp (hM.eventually (eventually_ge_atTop K))
  refine ⟨max J J', fun j hj => ?_⟩
  have hj1 : J ≤ j := (le_max_left _ _).trans hj
  have hj2 : J' ≤ j := (le_max_right _ _).trans hj
  have ht := signedVector_increasing_weight_tail_le u (w j) (hw j)
    (hwn j) (by positivity : 0 ≤ η / (4 * (B + 1))) (hJ' j hj2) htail
  have ht' : ‖(∑ n ∈ Finset.range (M j), w j n • u n) -
      ∑ n ∈ Finset.range K, w j n • u n‖ ≤ η / 2 := by
    apply ht.trans
    have hrat : B / (B + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      2 * w j (M j) * (η / (4 * (B + 1))) ≤
          2 * B * (η / (4 * (B + 1))) := by gcongr; exact hterminal j
      _ = (η / 2) * (B / (B + 1)) := by
        field_simp [ne_of_gt (show 0 < B + 1 by linarith)]
        ring
      _ ≤ η / 2 := mul_le_of_le_one_right (by positivity) hrat
  have hh : ‖(∑ n ∈ Finset.range K, w j n • u n) - signedVectorPrefix u K‖ < η / 4 := by
    simpa only [dist_eq_norm] using hJ j hj1
  have hkf' : ‖signedVectorPrefix u K - f‖ < η / 4 := by
    apply hKf.trans_le
    apply div_le_div_of_nonneg_left hη.le (by positivity)
    linarith
  rw [dist_eq_norm]
  have h1 := dist_triangle (∑ n ∈ Finset.range (M j), w j n • u n)
    (∑ n ∈ Finset.range K, w j n • u n) f
  have h2 := dist_triangle (∑ n ∈ Finset.range K, w j n • u n)
    (signedVectorPrefix u K) f
  simp only [dist_eq_norm] at h1 h2
  linarith

/-- The finite Abel identity centered at an arbitrary target. This retains
the signed complete prefix error before taking any norm. -/
theorem signedVector_increasing_weight_residual_identity
    (u : ℕ → E) (w : ℕ → ℝ) (f : E) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n • u n) - w 0 • f =
      w N • (signedVectorPrefix u (N + 1) - f) +
        ∑ n ∈ Finset.range N,
          (w n - w (n + 1)) • (signedVectorPrefix u (n + 1) - f) := by
  have htel : (∑ n ∈ Finset.range N, (w n - w (n + 1))) = w 0 - w N := by
    have h := Finset.sum_range_sub w N
    have hneg : (∑ n ∈ Finset.range N, (w n - w (n + 1))) =
        -(∑ n ∈ Finset.range N, (w (n + 1) - w n)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hneg, h]
    ring
  rw [signedVector_power_weight_identity]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, htel, sub_smul]
  abel

/-- Quantitative increasing Abel bound in terms of the exact prefix-error
envelope. Unlike a bound by twice the terminal weight, this keeps every
individual prefix rate and therefore allows unbounded terminal weights. -/
theorem signedVector_increasing_weight_residual_le
    (u : ℕ → E) (w : ℕ → ℝ) (f : E) (R : ℕ → ℝ)
    (hw : Monotone w) (hwn : ∀ n, 0 ≤ w n)
    (herror : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1))
    (N : ℕ) :
    ‖(∑ n ∈ Finset.range (N + 1), w n • u n) - w 0 • f‖ ≤
      w N * R (N + 1) +
        ∑ n ∈ Finset.range N, (w (n + 1) - w n) * R (n + 1) := by
  rw [signedVector_increasing_weight_residual_identity]
  calc
    _ ≤ ‖w N • (signedVectorPrefix u (N + 1) - f)‖ +
        ∑ n ∈ Finset.range N,
          ‖(w n - w (n + 1)) • (signedVectorPrefix u (n + 1) - f)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ _ := by
      apply add_le_add
      · rw [norm_smul, Real.norm_of_nonneg (hwn N)]
        exact mul_le_mul_of_nonneg_left (herror N) (hwn N)
      · apply Finset.sum_le_sum
        intro n hn
        have hdiff : 0 ≤ w (n + 1) - w n := sub_nonneg.mpr (hw (Nat.le_succ n))
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (herror n) hdiff

/-- A scalar Abel envelope bound transfers a full signed prefix rate with
only its displayed scalar multiplier. The envelope condition is ordinary
scalar analysis, separate from the arithmetic prefix-rate provider. -/
theorem signedVector_increasing_weight_rate_le
    (u : ℕ → E) (w : ℕ → ℝ) (f : E) (R : ℕ → ℝ)
    (hw : Monotone w) (hwn : ∀ n, 0 ≤ w n) (hwzero : w 0 = 1)
    (herror : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1))
    (N : ℕ) (A : ℝ)
    (henvelope : (∑ n ∈ Finset.range N, (w (n + 1) - w n) * R (n + 1)) ≤
      A * (w N * R (N + 1))) :
    ‖(∑ n ∈ Finset.range (N + 1), w n • u n) - f‖ ≤
      (1 + A) * (w N * R (N + 1)) := by
  have h := signedVector_increasing_weight_residual_le u w f R hw hwn herror N
  rw [hwzero, one_smul] at h
  calc
    _ ≤ w N * R (N + 1) +
        ∑ n ∈ Finset.range N, (w (n + 1) - w n) * R (n + 1) := h
    _ ≤ w N * R (N + 1) + A * (w N * R (N + 1)) :=
      add_le_add_right henvelope _
    _ = _ := by ring

/-- Exact scalar Abel budgets tending to zero give joint convergence,
even when the terminal weights are unbounded. No absolute summability
of the original vector series is assumed. -/
theorem signedVector_increasing_weights_budget_tendsto
    (u : ℕ → E) (f : E) (R : ℕ → ℝ)
    (herror : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1))
    (w : ℕ → ℕ → ℝ) (hw : ∀ j, Monotone (w j))
    (hwn : ∀ j n, 0 ≤ w j n) (hwzero : ∀ j, w j 0 = 1)
    (M : ℕ → ℕ)
    (hbudget : Tendsto (fun j => w j (M j) * R (M j + 1) +
      ∑ n ∈ Finset.range (M j), (w j (n + 1) - w j n) * R (n + 1))
      atTop (𝓝 0)) :
    Tendsto (fun j => ∑ n ∈ Finset.range (M j + 1), w j n • u n)
      atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hbudget η hη
  refine ⟨J, fun j hj => ?_⟩
  rw [dist_eq_norm]
  have h := signedVector_increasing_weight_residual_le u (w j) f R
    (hw j) (hwn j) herror (M j)
  rw [hwzero j, one_smul] at h
  apply h.trans_lt
  have hsmall := hJ j hj
  rw [dist_zero_right, Real.norm_eq_abs] at hsmall
  exact lt_of_le_of_lt (le_abs_self _) hsmall

/-- A uniform scalar envelope multiplier reduces joint Abel convergence
to the amplified endpoint rate alone. -/
theorem signedVector_increasing_weights_rate_tendsto
    (u : ℕ → E) (f : E) (R : ℕ → ℝ)
    (herror : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1))
    (w : ℕ → ℕ → ℝ) (hw : ∀ j, Monotone (w j))
    (hwn : ∀ j n, 0 ≤ w j n) (hwzero : ∀ j, w j 0 = 1)
    (M : ℕ → ℕ) (A : ℝ)
    (henvelope : ∀ j,
      (∑ n ∈ Finset.range (M j), (w j (n + 1) - w j n) * R (n + 1)) ≤
        A * (w j (M j) * R (M j + 1)))
    (hrate : Tendsto (fun j => w j (M j) * R (M j + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => ∑ n ∈ Finset.range (M j + 1), w j n • u n)
      atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  have hlim : Tendsto (fun j => (1 + A) * (w j (M j) * R (M j + 1)))
      atTop (𝓝 0) := by simpa using hrate.const_mul (1 + A)
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hlim η hη
  refine ⟨J, fun j hj => ?_⟩
  rw [dist_eq_norm]
  apply (signedVector_increasing_weight_rate_le u (w j) f R (hw j) (hwn j)
    (hwzero j) herror (M j) A (henvelope j)).trans_lt
  have hsmall := hJ j hj
  rw [dist_zero_right, Real.norm_eq_abs] at hsmall
  exact lt_of_le_of_lt (le_abs_self _) hsmall

end RiemannResearch.Analysis
