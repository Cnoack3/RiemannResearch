import RiemannResearch.RH.ParetoOrdinatePairError
import RiemannResearch.RH.ParetoTailCapacity
import RiemannResearch.Analysis.ProjectionCorrelationCompleteness

/-! # Centered fluctuations of the first-site Pareto residual at actual ordinates

The sample consists of every original positive zeta-zero occurrence up to T.
For each positive logarithmic frequency, covariance of the centered scalar
observation with its cosine recovers a nonconstant Pareto coordinate. The
conductor-two legal residue detects the remaining constant-frequency coordinate.
This yields an RH criterion in terms of vanishing unscaled empirical variance.
See Maples and Rodgers, https://arxiv.org/abs/1404.3080, for centered
mesoscopic zero statistics with a different normalization and sampling law.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis.ActualZeroOrdinate

/-- Mean of a scalar observation at the actual occurrence labels. -/
def occurrenceAverage (T : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∑ i : Copies T, f (copyOrdinate T i)) / (Ncount 0 T : ℝ)

/-- The scalar observation in direction v has this actual empirical mean. -/
def rowObservationMean (T : ℝ) (v : ThresholdHilbert) : ℝ :=
  inner ℝ (recovery T 0) v

theorem rowObservationMean_eq_average (T : ℝ) (v : ThresholdHilbert) :
    rowObservationMean T v = occurrenceAverage T (fun t => inner ℝ (cosineRow t) v) := by
  rw [rowObservationMean, recovery_zero_eq_mean, real_inner_smul_left, sum_inner]
  simp [occurrenceAverage, copyOrdinate, div_eq_mul_inv, mul_comm]

/-- Variance after subtracting the mean at this cutoff. -/
def rowObservationVariance (T : ℝ) (v : ThresholdHilbert) : ℝ :=
  occurrenceAverage T (fun t => (inner ℝ (cosineRow t) v - rowObservationMean T v) ^ 2)

/-- Covariance against the cosine of frequency log(k+1). Centering the first
factor already removes the product of the two empirical means. -/
def centeredCosineCovariance (T : ℝ) (v : ThresholdHilbert) (k : ℕ) : ℝ :=
  occurrenceAverage T (fun t => Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * t) *
    (inner ℝ (cosineRow t) v - rowObservationMean T v))

private theorem covariance_eq (T : ℝ) (v : ThresholdHilbert) (k : ℕ) :
    centeredCosineCovariance T v k = inner ℝ (recovery T k) v -
      rowObservationMean T v * occurrenceAverage T
        (fun t => Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * t)) := by
  rw [centeredCosineCovariance, recovery, real_inner_smul_left, sum_inner]
  simp only [occurrenceAverage, copyOrdinate, real_inner_smul_left, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  change ((∑ i : Copies T, Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * i.1.1.im) *
    inner ℝ (cosineRow i.1.1.im) v) -
    (∑ i : Copies T, Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * i.1.1.im)) *
      rowObservationMean T v) / (Ncount 0 T : ℝ) = (Ncount 0 T : ℝ)⁻¹ *
    (∑ i : Copies T, Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * i.1.1.im) *
      inner ℝ (cosineRow i.1.1.im) v) - rowObservationMean T v *
    ((∑ i : Copies T, Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * i.1.1.im)) / (Ncount 0 T : ℝ))
  ring

/-- The arithmetic covariance at a fixed nonzero frequency detects its coordinate. -/
theorem centeredCosineCovariance_tendsto (v : ThresholdHilbert) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun T => centeredCosineCovariance T v k) atTop
      (𝓝 ((1 / 2 : ℝ) * inner ℝ (paretoPointHilbert k) v)) := by
  have h₁ := (recovery_tendsto k).inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
  have h₀ := first_recovery_tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
  have hlog : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k+1 by omega))
  have hc := occurrence_cosine_mean_tendsto hlog.ne'
  have h := h₁.sub (h₀.mul hc)
  simpa only [covariance_eq, occurrenceAverage, copyOrdinate, rowObservationMean, diagonalMass,
    if_neg hk.ne', real_inner_smul_left, mul_zero, sub_zero] using h

/-- Finite Cauchy–Schwarz bounds each squared covariance by the empirical variance. -/
theorem centeredCosineCovariance_sq_le_variance (T : ℝ) (v : ThresholdHilbert) (k : ℕ) :
    centeredCosineCovariance T v k ^ 2 ≤ rowObservationVariance T v := by
  classical
  let x (i : Copies T) := inner ℝ (cosineRow (copyOrdinate T i)) v - rowObservationMean T v
  let y (i : Copies T) := Real.cos (Real.log ((k+1 : ℕ) : ℝ) * copyOrdinate T i)
  have hy : (∑ i : Copies T, y i ^ 2) ≤ (Ncount 0 T : ℝ) := by
    calc
      _ ≤ ∑ _i : Copies T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := pow_le_pow_left₀ (abs_nonneg (y i)) (Real.abs_cos_le_one _) 2
        simpa only [sq_abs, one_pow] using h
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, mul_one]
  have hx : 0 ≤ ∑ i : Copies T, x i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y x
  have hb : (∑ i : Copies T, y i * x i) ^ 2 ≤ (∑ i : Copies T, x i ^ 2) * (Ncount 0 T : ℝ) := by
    exact hs.trans ((mul_le_mul_of_nonneg_right hy hx).trans_eq (mul_comm _ _))
  change ((∑ i : Copies T, y i * x i) / (Ncount 0 T : ℝ)) ^ 2 ≤
    (∑ i : Copies T, x i ^ 2) / (Ncount 0 T : ℝ)
  by_cases hn : Ncount 0 T = 0
  · simp [hn]
  · have hN : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [div_pow]
    calc
      _ ≤ ((∑ i : Copies T, x i ^ 2) * (Ncount 0 T : ℝ)) / (Ncount 0 T : ℝ)^2 :=
        div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ = _ := by field_simp [hN]

/-- The residual of the physical point at integer one. -/
def firstSiteResidual : ThresholdHilbert :=
  closedSpaceᗮ.starProjection (paretoPointHilbert 0)

private theorem firstSiteResidual_zero_iff : firstSiteResidual = 0 ↔ RiemannHypothesis := by
  rw [rh_iff_first_site_vacancy_zero, ← first_site_residual_sq]
  change firstSiteResidual = 0 ↔ ‖firstSiteResidual‖ ^ 2 = 0
  simp

/-- An orthogonal vector invisible to every nonzero cosine coordinate would be
supported at the first site. The legal conductor-two atom is nonzero there. -/
private theorem orthogonal_eq_zero_of_tail (v : ThresholdHilbert) (hv : v ∈ closedSpaceᗮ)
    (h : ∀ k : ℕ, 0 < k → inner ℝ (paretoPointHilbert k) v = 0) : v = 0 := by
  have htail (k : ℕ) (hk : k ≠ 0) : hilbertGibbsPhysical v k = 0 := by
    have he := h k (Nat.pos_of_ne_zero hk)
    rw [real_inner_comm, inner_paretoPoint] at he
    exact (mul_eq_zero.mp he).resolve_left (paretoWeight_pos k).ne'
  have hmem : residueAtom 0 ∈ closedSpace :=
    RiemannResearch.Analysis.ProjectionCorrelationCompleteness.atom_mem_dictionaryClosure
      residueAtom 0
  have he := (closedSpace.mem_orthogonal v).mp hv (residueAtom 0) hmem
  rw [hilbertGibbs_inner_physical] at he
  rw [tsum_eq_single 0 (fun k hk => by simp [htail k hk])] at he
  have ha : hilbertGibbsPhysical (residueAtom 0) 0 = (1 / 2 : ℝ) := by
    simpa [hilbertGibbsPhysical_eq, anchoredEvaluationCLM_apply] using
      TailCapacity.residueAtom_evaluation 0
  rw [ha] at he
  have hzero : hilbertGibbsPhysical v 0 = 0 := by
    have hh := (mul_eq_zero.mp he).resolve_left (paretoWeight_pos 0).ne'
    linarith only [hh]
  apply Subtype.ext
  funext k
  change v k = 0
  have hk : hilbertGibbsPhysical v k = 0 := by
    by_cases h0 : k = 0
    · simpa [h0] using hzero
    · exact htail k h0
  exact (div_eq_zero_iff.mp hk).resolve_right (Real.sqrt_pos.mpr (paretoWeight_pos k)).ne'

/-- Even along a single sequence of unbounded cutoffs, collapse of this centered
variance is equivalent to mathlib's RH. No fluctuation law is assumed. -/
theorem rh_iff_centered_firstSiteVariance {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop) :
    RiemannHypothesis ↔
      Tendsto (fun n => rowObservationVariance (τ n) firstSiteResidual) atTop (𝓝 0) := by
  constructor
  · intro h
    simp [firstSiteResidual_zero_iff.mpr h, rowObservationVariance, rowObservationMean,
      occurrenceAverage]
  · intro hvar
    apply firstSiteResidual_zero_iff.mp
    apply orthogonal_eq_zero_of_tail firstSiteResidual (closedSpaceᗮ.starProjection_apply_mem _)
    intro k hk
    have hc := (centeredCosineCovariance_tendsto firstSiteResidual hk).comp hτ
    have hb : ((1 / 2 : ℝ) * inner ℝ (paretoPointHilbert k) firstSiteResidual)^2 ≤ 0 :=
      le_of_tendsto_of_tendsto' (hc.pow 2) hvar
        (fun n => centeredCosineCovariance_sq_le_variance (τ n) firstSiteResidual k)
    nlinarith only [hb]

/-- A fixed nonconstant covariance bounds the variance from below at all sufficiently
large cutoffs if RH fails. -/
theorem eventual_positive_firstSiteVariance_of_not_rh (hn : ¬ RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, c ≤ rowObservationVariance T firstSiteResidual := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ inner ℝ (paretoPointHilbert k) firstSiteResidual ≠ 0 := by
    by_contra h
    apply hn
    apply firstSiteResidual_zero_iff.mp
    apply orthogonal_eq_zero_of_tail firstSiteResidual (closedSpaceᗮ.starProjection_apply_mem _)
    intro k hk
    by_contra hne
    exact h ⟨k, hk, hne⟩
  obtain ⟨k, hk, hne⟩ := hex
  let m : ℝ := (1 / 2 : ℝ) * inner ℝ (paretoPointHilbert k) firstSiteResidual
  have hm : 0 < m^2 := sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hne)
  have hlim : Tendsto (fun T => centeredCosineCovariance T firstSiteResidual k ^ 2)
      atTop (𝓝 (m^2)) := (centeredCosineCovariance_tendsto firstSiteResidual hk).pow 2
  have hpos : ∀ᶠ T : ℝ in atTop, m^2/2 < centeredCosineCovariance T firstSiteResidual k ^ 2 :=
    hlim (Ioi_mem_nhds (show m^2/2 < m^2 by linarith only [hm]))
  refine ⟨m^2/2, by linarith only [hm], ?_⟩
  filter_upwards [hpos] with T hT
  exact hT.le.trans (centeredCosineCovariance_sq_le_variance T firstSiteResidual k)

/-- The standardized scalar observations have uniformly bounded support if RH fails. -/
theorem standardized_firstSiteResidual_bounded_of_not_rh (hn : ¬ RiemannHypothesis) :
    ∃ B : ℝ, ∀ᶠ T : ℝ in atTop, ∀ t : ℝ,
      |(inner ℝ (cosineRow t) firstSiteResidual - rowObservationMean T firstSiteResidual) /
        Real.sqrt (rowObservationVariance T firstSiteResidual)| ≤ B := by
  obtain ⟨c, hc, hv⟩ := eventual_positive_firstSiteVariance_of_not_rh hn
  let m := inner ℝ (paretoPointHilbert 0) firstSiteResidual
  have hmean : Tendsto (fun T => rowObservationMean T firstSiteResidual) atTop (𝓝 m) :=
    first_recovery_tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := firstSiteResidual))
  refine ⟨(‖firstSiteResidual‖ + |m| + 1) / Real.sqrt c, ?_⟩
  filter_upwards [hv, hmean.abs.eventually_lt_const (show |m| < |m|+1 by linarith)]
    with T hvar hT
  intro t
  have hx : |inner ℝ (cosineRow t) firstSiteResidual| ≤ ‖firstSiteResidual‖ :=
    (abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_right
      (cosineRow_norm_le_one t) (norm_nonneg _)).trans_eq (one_mul _))
  have hy : |inner ℝ (cosineRow t) firstSiteResidual - rowObservationMean T firstSiteResidual|
      ≤ ‖firstSiteResidual‖ + |m| + 1 := by
    have hs := abs_sub (inner ℝ (cosineRow t) firstSiteResidual)
      (rowObservationMean T firstSiteResidual)
    linarith only [hs, hx, hT]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right hy (Real.sqrt_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hc) (Real.sqrt_le_sqrt hvar))

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_centered_firstSiteVariance' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_centered_firstSiteVariance

end RiemannResearch.RH.Pareto.OrdinateCosine
