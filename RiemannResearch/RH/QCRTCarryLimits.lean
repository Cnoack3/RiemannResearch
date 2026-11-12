import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.ScreenedCarry

/-!
# Stage-dependent CRT carry limits in the complete Hilbert norm

The same finite identity applies after a continuous change of measure.
Changing prime projections have an explicit error term. Only the combined
finite approximants are assumed to converge; no separate unordered prime
or carry series is assumed.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ScreenedCarry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact accounting for a changing screening space, with contraction on
the approximation error and a separate projection-motion term. -/
theorem moving_carry_error (V W : Submodule ℝ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (a c f target : H) (ha : a ∈ V) (heq : f = a - c) :
    ‖screen V c + screen W target‖ ≤
      ‖f-target‖ + ‖V.starProjection target-W.starProjection target‖ := by
  have hs : screen V c = -screen V f := by
    rw [heq, map_sub, screen_of_mem V ha, zero_sub, neg_neg]
  have he : screen V c + screen W target =
      -screen V (f-target) +
        (V.starProjection target-W.starProjection target) := by
    rw [hs, map_sub]
    simp only [screen_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖-screen V (f-target)‖ +
        ‖V.starProjection target-W.starProjection target‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_neg]
      exact add_le_add
        (ProjectionCompression.defect_norm_le V (f-target)) le_rfl

theorem moving_carry_tendsto (V : ℕ → Submodule ℝ H) (W : Submodule ℝ H)
    [∀ j, (V j).HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (a c f : ℕ → H) (target : H)
    (ha : ∀ j, a j ∈ V j) (heq : ∀ j, f j = a j-c j)
    (hf : Tendsto f atTop (𝓝 target))
    (hproj : Tendsto (fun j => (V j).starProjection target)
      atTop (𝓝 (W.starProjection target))) :
    Tendsto (fun j => screen (V j) (c j)) atTop (𝓝 (-screen W target)) := by
  have hn : Tendsto (fun j => ‖f j-target‖ +
      ‖(V j).starProjection target-W.starProjection target‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, add_zero] using
      ((hf.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => target) atTop (𝓝 target))).norm).add
        ((hproj.sub (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => W.starProjection target) atTop (𝓝 (W.starProjection target)))).norm)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hn.eventually (gt_mem_nhds hε)] with j hj
  rw [dist_eq_norm, sub_neg_eq_add]
  exact (moving_carry_error (V j) W (a j) (c j) (f j) target (ha j) (heq j)).trans_lt hj

end RiemannResearch.Analysis.ScreenedCarry

namespace RiemannResearch.RH.QCRTCarryLimits
open ZetaTwoHilbert QSimultaneousCRT
open RiemannResearch.Analysis.ScreenedCarry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Residualized canonical carries are independent of all finite prime
synthesis details, also after a continuous measure transfer. -/
theorem screen_transported_carry (L : QHilbert →L[ℝ] H)
    (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (d : ℕ) (hd : L (primeSynthesis d) ∈ W) :
    screen W (L (canonicalCarry d)) = -screen W (L (qResidue d)) := by
  rw [canonicalCarry_eq, map_sub, map_sub, screen_of_mem W hd, zero_sub]

theorem transported_carry_gram (L : QHilbert →L[ℝ] H)
    (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (d e : ℕ) (hd : L (primeSynthesis d) ∈ W) (he : L (primeSynthesis e) ∈ W) :
    inner ℝ (screen W (L (canonicalCarry d))) (screen W (L (canonicalCarry e))) =
      inner ℝ (screen W (L (qResidue d))) (screen W (L (qResidue e))) := by
  rw [screen_transported_carry L W d hd, screen_transported_carry L W e he,
    inner_neg_left, inner_neg_right, neg_neg]

/-- Each stage has its own finite set and coefficients. -/
theorem finite_transported_screened_carry (L : QHilbert →L[ℝ] H)
    (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, L (primeSynthesis d) ∈ W) :
    screen W (L (∑ d ∈ s, c d • canonicalCarry d)) =
      -screen W (L (∑ d ∈ s, c d • qResidue d)) := by
  simp only [map_sum, map_smul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [screen_transported_carry L W d (hs d hd), smul_neg]

/-- Combined finite-block convergence and strong convergence of the prime
projections at the target are the exact hypotheses. -/
theorem finite_block_carry_limit (L : QHilbert →L[ℝ] H)
    (Wj : ℕ → Submodule ℝ H) (W : Submodule ℝ H)
    [∀ j, (Wj j).HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (target : H)
    (hs : ∀ j d, d ∈ s j → L (primeSynthesis d) ∈ Wj j)
    (hf : Tendsto (fun j => L (∑ d ∈ s j, c j d • qResidue d))
      atTop (𝓝 target))
    (hproj : Tendsto (fun j => (Wj j).starProjection target)
      atTop (𝓝 (W.starProjection target))) :
    Tendsto (fun j => screen (Wj j) (L (∑ d ∈ s j, c j d • canonicalCarry d)))
      atTop (𝓝 (-screen W target)) := by
  apply moving_carry_tendsto Wj W
    (fun j => L (∑ d ∈ s j, c j d • primeSynthesis d))
    (fun j => L (∑ d ∈ s j, c j d • canonicalCarry d))
    (fun j => L (∑ d ∈ s j, c j d • qResidue d)) target
  · intro j
    simp only [map_sum, map_smul]
    exact (Wj j).sum_mem fun d hd => (Wj j).smul_mem _ (hs j d hd)
  · intro j
    rw [finite_synthesis_identity, map_sub]
  · exact hf
  · exact hproj

end RiemannResearch.RH.QCRTCarryLimits
