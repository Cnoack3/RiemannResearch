import RiemannResearch.Analysis.MontgomeryFiniteIndexGap
import RiemannResearch.Analysis.MicroscopicRankTail
import RiemannResearch.Analysis.MicroscopicCountTail
import RiemannResearch.Analysis.ZeroDPPWindowLattice

/-!
# Rank truncation of the translated count variance

The approximation retains the complete equal-ordinate term and the positive
pairs up to a prescribed chronological rank. Integrating the omitted positive
pair mass gives the exact error. One truncated second moment at width twice
the largest width bounds all ranks and all smaller widths simultaneously.
-/

noncomputable section

open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroWindowVariance ActualZeroCollisionCertificate
open MicroscopicRankCover MicroscopicCountTail ZeroDPPCollisionLoss
open ZeroDPPCorrelation ZeroDPPRankVacancy

theorem finiteIndexGapMass_width_mono {T : ℝ} (hT : 1 < T) (J : ℕ) :
    Monotone (fun r => finiteIndexGapMass T r J) := by
  intro u v huv
  apply Finset.sum_le_sum
  intro d _
  apply div_le_div_of_nonneg_right _ (show 0 ≤ normalizer T from
    (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).le)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i + d < Ncount 0 T
  · simp only [if_pos hi]
    let g := unfoldingScale T * (cutoffOrdinate T (i + d) - cutoffOrdinate T i)
    change (if 0 < g ∧ g ≤ u then (1 : ℝ) else 0) ≤ (if 0 < g ∧ g ≤ v then 1 else 0)
    by_cases h : 0 < g ∧ g ≤ u
    · rw [if_pos h, if_pos ⟨h.1, h.2.trans huv⟩]
    · rw [if_neg h]
      split_ifs <;> norm_num
  · simp only [if_neg hi, le_rfl]

private theorem rankTail_width_mono {T : ℝ} (hT : 1 < T) (J : ℕ) :
    Monotone (fun r => actualRankTail T r J) := by
  intro u v huv
  have hL : 0 < Real.log T / (2 * Real.pi) := div_pos (Real.log_pos hT) (by positivity)
  have hD : 0 ≤ normalizer T :=
    (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).le
  apply div_le_div_of_nonneg_right _ hD
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  let g := cutoffOrdinate T j - cutoffOrdinate T i
  let L := Real.log T / (2 * Real.pi)
  change (if i + J < j ∧ g ≤ u / L then (1 : ℝ) else 0) ≤
    (if i + J < j ∧ g ≤ v / L then 1 else 0)
  by_cases h : i + J < j ∧ g ≤ u / L
  · rw [if_pos h, if_pos ⟨h.1, h.2.trans (div_le_div_of_nonneg_right huv hL.le)⟩]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- All equal-height ordered pairs are retained at every rank, including ranks
larger than J. Strict gaps contribute in both orientations through integration. -/
def finiteRankWindowVariance (T r : ℝ) (J : ℕ) : ℝ :=
  r * ((actualCollision T : ℝ) / normalizer T) +
    2 * (∫ u in (0 : ℝ)..r, finiteIndexGapMass T u J) - unfoldedWindowMean T r ^ 2

/-- The identity holds at one height threshold for an entire bounded interval
of widths, with every collision included, even at J = 0. -/
theorem eventually_variance_sub_finiteRank_eq (Q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ Q → ∀ J : ℕ,
      unfoldedWindowVariance T r - finiteRankWindowVariance T r J =
        2 * ∫ u in (0 : ℝ)..r, positiveGapMass T u - finiteIndexGapMass T u J := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_supported_width Q] with T hT hs
  intro r hr hrQ J
  obtain ⟨hw, hf⟩ := hs r hr hrQ
  have ht := zero_lt_one.trans hT
  have hm : (Ncount 0 T : ℝ) * (r / (Real.log T / (2 * Real.pi))) =
      T * unfoldedWindowMean T r := by
    unfold unfoldedWindowMean
    field_simp [ht.ne']
  have hv := actual_triangle_eq_mean_sq_add_variance T _ _ ht hw hf hm
  change actualPhysicalTriangleEnergy T (r / (Real.log T / (2 * Real.pi))) =
    unfoldedWindowMean T r ^ 2 + unfoldedWindowVariance T r at hv
  rw [physicalTriangle_eq_collision_add_positive_gaps hT hr] at hv
  rw [finiteRankWindowVariance, normalizer, intervalIntegral.integral_sub
    (positiveGapMass_mono hT).intervalIntegrable (finiteIndexGapMass_width_mono hT J).intervalIntegrable]
  linarith only [hv]

/-- The truncation error is one-sided and at most twice the width times the
collision-inclusive rank tail at the largest width. -/
theorem eventually_variance_sub_finiteRank_bounds (Q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ Q → ∀ J : ℕ,
      0 ≤ unfoldedWindowVariance T r - finiteRankWindowVariance T r J ∧
      unfoldedWindowVariance T r - finiteRankWindowVariance T r J ≤
        2 * r * actualRankTail T Q J := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_variance_sub_finiteRank_eq Q] with T hT he
  intro r hr hrQ J
  rw [he r hr hrQ J]
  have hP := (positiveGapMass_mono hT).intervalIntegrable (a := 0) (b := r) (μ := volume)
  have hF := (finiteIndexGapMass_width_mono hT J).intervalIntegrable (a := 0) (b := r) (μ := volume)
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hr (fun u _ =>
      sub_nonneg.mpr (finiteIndexGapMass_le_positiveGapMass hT u J)))
  · have hb := intervalIntegral.integral_mono_on (μ := volume) hr (hP.sub hF)
        (g := fun _ : ℝ => actualRankTail T Q J) intervalIntegrable_const (fun u hu =>
          (le_abs_self _).trans ((positiveGapMass_sub_finiteIndexGapMass_le hT u J).trans
            (rankTail_width_mono hT J (hu.2.trans hrQ))))
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hb
    linarith only [hb]

/-- The truncated second moment supplies an unconditional error bound at
every rank and width, with no asymptotic distribution premise. -/
theorem eventually_variance_sub_finiteRank_truncated {Q : ℝ} (hQ : 0 < Q) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ Q → ∀ J : ℕ,
      unfoldedWindowVariance T r - finiteRankWindowVariance T r J ≤
        (2 * r / Q) * truncatedWindowSecondMoment T (2 * Q) J := by
  filter_upwards [eventually_rankTail_le_truncated hQ, eventually_variance_sub_finiteRank_bounds Q]
    with T htail hb
  intro r hr hrQ J
  calc
    _ ≤ 2 * r * actualRankTail T Q J := (hb r hr hrQ J).2
    _ ≤ 2 * r * (truncatedWindowSecondMoment T (2 * Q) J / Q) :=
      mul_le_mul_of_nonneg_left (htail J) (by positivity)
    _ = _ := by ring

/-- A translated count-tail bound only at 2Q suffices for uniform exponential
variance approximation on [0,Q]. The height threshold is independent of J and r. -/
theorem eventually_variance_sub_finiteRank_exp {Q : ℝ} (hQ : 0 < Q)
    (hcounts : ExpTranslatedCountTail (2 * Q)) :
    ∃ A c : ℝ, 0 ≤ A ∧ 0 < c ∧ ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ Q →
      ∀ J : ℕ, 0 ≤ unfoldedWindowVariance T r - finiteRankWindowVariance T r J ∧
        unfoldedWindowVariance T r - finiteRankWindowVariance T r J ≤
          A * Real.exp (-(c * (J : ℝ))) := by
  obtain ⟨B, c, hB, hc, htail⟩ := eventually_rankTail_le_exp hQ
    (expTranslatedSquareTail_of_exceedances hcounts)
  refine ⟨2 * Q * B, c, by positivity, hc, ?_⟩
  filter_upwards [htail, eventually_variance_sub_finiteRank_bounds Q] with T hT hb
  intro r hr hrQ J
  obtain ⟨hlo, hhi⟩ := hb r hr hrQ J
  refine ⟨hlo, hhi.trans ?_⟩
  calc
    2 * r * actualRankTail T Q J ≤ 2 * r * (B * Real.exp (-(c * (J : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hT J) (by positivity)
    _ ≤ 2 * Q * (B * Real.exp (-(c * (J : ℝ)))) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hB (Real.exp_pos _).le)
    _ = _ := by ring

/-- Third moments already suffice when both the width and the chronological
rank vary with T. Only an upper bound on the width and divergence of the
rank are required. -/
theorem tendsto_variance_sub_movingFiniteRank {Q : ℝ} (hQ : 0 < Q)
    (hthird : ZeroDPPVacancyDensity.BoundedTranslatedThirdMoment (2 * Q))
    (r : ℝ → ℝ) (J : ℝ → ℕ) (hr : ∀ᶠ T : ℝ in atTop, 0 ≤ r T ∧ r T ≤ Q)
    (hJ : Tendsto J atTop atTop) :
    Tendsto (fun T => unfoldedWindowVariance T (r T) -
      finiteRankWindowVariance T (r T) (J T)) atTop (𝓝 0) := by
  obtain ⟨C, hC, ht⟩ := eventually_rankTail_le_third hQ hthird
  have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hJ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hreal.const_div_atTop (2 * C))
  · filter_upwards [hr, eventually_variance_sub_finiteRank_bounds Q] with T hw hb
    exact (hb _ hw.1 hw.2 _).1
  · filter_upwards [hr, ht, hJ.eventually_gt_atTop 0, eventually_variance_sub_finiteRank_bounds Q]
      with T hw htail hj hb
    have hj' : (0 : ℝ) < J T := by exact_mod_cast hj
    have hpos : 0 ≤ C / (Q * (J T : ℝ)) := div_nonneg hC (mul_nonneg hQ.le hj'.le)
    calc
      _ ≤ 2 * r T * actualRankTail T Q (J T) := (hb _ hw.1 hw.2 _).2
      _ ≤ 2 * r T * (C / (Q * J T)) :=
        mul_le_mul_of_nonneg_left (htail _ hj) (mul_nonneg (by norm_num) hw.1)
      _ ≤ 2 * Q * (C / (Q * J T)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw.2 (by norm_num)) hpos
      _ = 2 * C / (J T : ℝ) := by field_simp [hQ.ne', hj'.ne'] <;> ring

/-- A single divergent rank schedule works at every rational width. The
short-window second-moment upper bound is used in the forward implication
through the existing actual-variance criterion. -/
theorem positiveGapPCC_iff_movingFiniteRankVariance (hUpper : ShortWindowSecondMomentUpper)
    (hthird : ∀ q : ℚ, 0 < q → ZeroDPPVacancyDensity.BoundedTranslatedThirdMoment (2 * (q : ℝ)))
    (J : ℝ → ℕ) (hJ : Tendsto J atTop atTop) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto
      (fun T => finiteRankWindowVariance T q (J T)) atTop (𝓝 (sineWindowEnergy q - (q : ℝ) ^ 2)) := by
  rw [positiveGapPCC_iff_rationalSineWindowVariance hUpper]
  have he (q : ℚ) (hq : 0 < q) :
      Tendsto (fun T => unfoldedWindowVariance T q - finiteRankWindowVariance T q (J T))
        atTop (𝓝 0) :=
    tendsto_variance_sub_movingFiniteRank (by exact_mod_cast hq) (hthird q hq) (fun _ => q) J
      (Eventually.of_forall (fun _ => ⟨by exact_mod_cast hq.le, le_rfl⟩)) hJ
  constructor
  · intro h q hq
    simpa only [sub_zero, sub_sub_cancel] using (h q hq).sub (he q hq)
  · intro h q hq
    simpa only [zero_add, sub_add_cancel] using (he q hq).add (h q hq)

end RiemannResearch.Analysis.MontgomeryPositiveGap
