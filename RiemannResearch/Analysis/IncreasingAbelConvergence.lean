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

end RiemannResearch.Analysis
