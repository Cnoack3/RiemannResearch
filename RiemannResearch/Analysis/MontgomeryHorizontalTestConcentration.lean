import RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
import RiemannResearch.Analysis.ActualOneSidedHorizontalDisplacement

/-! # Signed test defects on actual zeta zero occurrences

This combines the exceptional-pair estimates (Lamzouri, arXiv:2611.14486,
§§2–3) with the one-sided horizontal concentration criterion. The Fourier
test envelope and its retained-strip Taylor bound are explicit hypotheses.
For a real-part Taylor estimate the array is the real part of the signed
complex-minus-ordinate defect, embedded in ℂ.
-/
noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology Classical
namespace RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
open ActualZeroOrdinate MontgomeryExceptionalPairs

private def exceptionalCopies (T δ : ℝ) : Finset (Copies T) :=
  Finset.univ.filter fun i => δ / Real.log T < copyDisplacement T i

private theorem exceptionalCopies_card (T δ : ℝ) :
    ((exceptionalCopies T δ).card : ℝ) = strictTail T (δ / Real.log T) := by
  classical
  unfold exceptionalCopies strictTail FiniteStrictTail.tail
  rw [← Finset.sum_filter]
  simp

/-- A global exponential majorant and a quadratic bound on retained pairs
suffice for convergence of the entire signed test defect. The near-strip
height threshold may depend on the width. -/
theorem signed_test_defect_tendsto_of_uniformSelbergDensity
    {a : ℝ} (hD : UniformSelbergDensity a) (hRows : FujiiMicroscopicRowMoments)
    (hMean : Tendsto oneSidedHeightMean atTop (𝓝 0))
    {θ A C : ℝ} (hθ : 0 < θ) (hθmax : 2 * θ < a) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (F : (T : ℝ) → Copies T × Copies T → ℂ)
    (hEnv : ∀ᶠ T : ℝ in atTop, ∀ e, ‖F T e‖ ≤ A *
      (((Ncount 0 T : ℝ)⁻¹ * gapWeight T e.1 e.2) *
        Real.exp (θ * (mark T e.1 + mark T e.2))))
    (hTaylor : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ᶠ T : ℝ in atTop,
      ∀ i j : Copies T, mark T i ≤ δ → mark T j ≤ δ →
        ‖F T (i,j)‖ ≤ C * δ ^ 2 * ((Ncount 0 T : ℝ)⁻¹ * gapWeight T i j)) :
    Tendsto (fun T : ℝ => ∑ e ∈ (Finset.univ : Finset (Copies T)) ×ˢ Finset.univ,
      F T e) atTop (𝓝 0) := by
  classical
  have ha : 0 < a := by linarith only [hθ, hθmax]
  have hconc := (oneSidedHeightMean_tendsto_zero_iff ha hD).mp hMean
  have hratio : 2 * θ / a < 1 := (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hθmax)
  let κ := (1 - 2 * θ / a) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith only [hratio]
  have hgap : κ < 1 - 2 * θ / a := by dsimp [κ]; linarith only [hratio]
  obtain ⟨B, hB, hdel⟩ :=
    eventually_signed_deletion_le_of_uniformSelbergDensity ha hD hRows hθ hκ.le hgap hA
  obtain ⟨K, hK, hrow⟩ := hRows 1 (by norm_num)
  rw [Metric.tendsto_nhds]
  intro d hd
  let δ := min 1 (d / (2 * (C*K + 1)))
  have hCK := mul_nonneg hC hK
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ^2 ≤ δ := by nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  have hscale : C * δ^2 * K ≤ d / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * (C*K + 1) by positivity)).mp
      (show δ ≤ d / (2 * (C*K + 1)) from min_le_right _ _)
    nlinarith only [hh, mul_le_mul_of_nonneg_left hδ2 hCK, hδ.le]
  have hfrac : Tendsto (fun T : ℝ => ((exceptionalCopies T δ).card : ℝ) / (Ncount 0 T : ℝ))
      atTop (𝓝 0) := by simpa only [exceptionalCopies_card] using hconc δ hδ
  have hdec := (hfrac.rpow_const_nhds_zero hκ).const_mul B
  rw [mul_zero] at hdec
  have hsmall := hdec.eventually (Iio_mem_nhds (show (0:ℝ) < d/2 by positivity))
  filter_upwards [hrow, hsmall, hdel, hTaylor δ hδ hδ1, hEnv, eventually_gt_atTop (1:ℝ)]
    with T hrow hsmall hdel hTaylor hEnv hT
  let U : Finset (Copies T) := Finset.univ
  let G := U \ exceptionalCopies T δ
  let w := fun e : Copies T × Copies T => (Ncount 0 T : ℝ)⁻¹ * gapWeight T e.1 e.2
  have hw (e : Copies T × Copies T) : 0 ≤ w e :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (gapWeight_nonneg _ _ _)
  have hmass : (∑ e ∈ U ×ˢ U, w e) ≤ K := by
    rw [Finset.sum_product]
    simpa only [U, w, rowMass, Finset.mul_sum, pow_one] using hrow
  have hmark {i : Copies T} (hi : i ∈ G) : mark T i ≤ δ := by
    have hn := (Finset.mem_sdiff.mp hi).2
    have hdisp : copyDisplacement T i ≤ δ / Real.log T := by
      simpa [exceptionalCopies] using hn
    simpa only [mark, mul_comm] using (le_div_iff₀ (Real.log_pos hT)).mp hdisp
  have hGG : G ×ˢ G ⊆ U ×ˢ U := by
    intro e he
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  have hret : ‖∑ e ∈ G ×ˢ G, F T e‖ ≤ C * δ^2 * K := by
    calc
      _ ≤ ∑ e ∈ G ×ˢ G, ‖F T e‖ := norm_sum_le _ _
      _ ≤ ∑ e ∈ G ×ˢ G, C * δ^2 * w e := Finset.sum_le_sum fun e he =>
        hTaylor e.1 e.2 (hmark (Finset.mem_product.mp he).1) (hmark (Finset.mem_product.mp he).2)
      _ = C * δ^2 * ∑ e ∈ G ×ˢ G, w e := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg hGG (fun e _ _ => hw e)).trans hmass)
        (mul_nonneg hC (sq_nonneg δ))
  have hdiff := hdel (exceptionalCopies T δ) (F T) (fun e _ => hEnv e)
  change ‖(∑ e ∈ U ×ˢ U, F T e) - (∑ e ∈ G ×ˢ G, F T e)‖ ≤ _ at hdiff
  change B * (((exceptionalCopies T δ).card : ℝ) / (Ncount 0 T : ℝ)) ^ κ < d / 2 at hsmall
  rw [dist_zero_right]
  have ht := norm_add_le ((∑ e ∈ U ×ˢ U, F T e) - (∑ e ∈ G ×ˢ G, F T e))
    (∑ e ∈ G ×ˢ G, F T e)
  rw [sub_add_cancel] at ht
  linarith only [ht, hdiff, hsmall, hret, hscale]

/-- Specialize the one-slope criterion to the published strict Conrey–Baluyot range. -/
theorem signed_test_defect_tendsto_of_oneSidedHeightMean
    (hD : ConreyBaluyotDensityHypothesis) (hRows : FujiiMicroscopicRowMoments)
    (hMean : Tendsto oneSidedHeightMean atTop (𝓝 0))
    {θ A C : ℝ} (hθ : 0 < θ) (hθmax : θ < 4 / 7) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (F : (T : ℝ) → Copies T × Copies T → ℂ)
    (hEnv : ∀ᶠ T : ℝ in atTop, ∀ e, ‖F T e‖ ≤ A *
      (((Ncount 0 T : ℝ)⁻¹ * gapWeight T e.1 e.2) *
        Real.exp (θ * (mark T e.1 + mark T e.2))))
    (hTaylor : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ᶠ T : ℝ in atTop,
      ∀ i j : Copies T, mark T i ≤ δ → mark T j ≤ δ →
        ‖F T (i,j)‖ ≤ C * δ ^ 2 * ((Ncount 0 T : ℝ)⁻¹ * gapWeight T i j)) :
    Tendsto (fun T : ℝ => ∑ e ∈ (Finset.univ : Finset (Copies T)) ×ˢ Finset.univ,
      F T e) atTop (𝓝 0) := by
  obtain ⟨a, hlow, hhigh⟩ := exists_between (show 2 * θ < 8 / 7 by linarith only [hθmax])
  have ha : 0 < a := by linarith only [hθ, hlow]
  exact signed_test_defect_tendsto_of_uniformSelbergDensity (hD a ha hhigh) hRows
    hMean hθ hlow hA hC F hEnv hTaylor


/--
info: 'RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs.signed_test_defect_tendsto_of_oneSidedHeightMean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signed_test_defect_tendsto_of_oneSidedHeightMean

end RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
