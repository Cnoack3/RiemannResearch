import RiemannResearch.Analysis.MontgomeryPrimeProbeCesaro
import RiemannResearch.Analysis.MontgomeryWindowPairCorrelation
import RiemannResearch.Analysis.MontgomerySmoothSampleDrift

/-!
# The width average of the actual signed prime–zero trace

Averages use the two-sided normalization `2 / R`. Positive gaps exclude all
equal ordinates, including distinct occurrences; the complete equal-ordinate
mass is retained separately. The gamma main count is sampled at the same
clipped forward endpoints as the actual discrepancy.

Goldston, Lee, Schettler and Suriajaya, *Pair Correlation Conjecture for the
zeros of the Riemann zeta-function I*, §6, (6.2), arXiv:2503.15449, motivates
the finite triangle decomposition and the growing-width analytical input.
The transfer lemmas below display that input explicitly.
-/

noncomputable section

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set Zeta23 MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroDiscrepancy
open ActualZeroCollisionCertificate ActualZeroWindowVariance
open scoped BigOperators Topology

/-- The complete normalized equal-ordinate mass, with all ordered occurrences. -/
def normalizedOrdinateCollision (T : ℝ) : ℝ :=
  (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))

/-- The width average of the signed pair statistic sampled at the true ordinates. -/
def cesaroArgumentIncrement (T R : ℝ) : ℝ :=
  (2 / R) * ∫ q in (0 : ℝ)..R, sampledArgumentIncrement T q

/-- Signed width average of the drift of the actually sampled gamma main count. -/
def cesaroSmoothDrift (T R : ℝ) : ℝ :=
  (2 / R) * ∫ q in (0 : ℝ)..R, q - sampledHeightIncrement smoothCount T q

/-- The actual signed comparison integrated on the full initial width interval. -/
def cesaroSignedTrace (T R : ℝ) : ℝ :=
  (2 / R) * ∫ q in (0 : ℝ)..R, sampledArgumentIncrement T q + primeProbeEnergy T q

/-- Clipping, multiplicities and strict positive gaps lead to the same exact
gamma-count decomposition at every positive width. -/
theorem sampledArgumentIncrement_eq_gap_sub_smooth {T q : ℝ} (hT : 1 < T) (hq : 0 < q) :
    sampledArgumentIncrement T q =
      positiveGapMass T q - sampledHeightIncrement smoothCount T q := by
  classical
  have hL : 0 < unfoldingScale T := div_pos (Real.log_pos hT) (by positivity)
  have hp := positiveGapMass_eq_ordinate_window_counts hT (div_pos hq hL)
  rw [div_mul_cancel₀ _ hL.ne'] at hp
  rw [hp, sampledArgumentIncrement, sampledHeightIncrement, sampledHeightIncrement,
    ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let t := copyOrdinate T i
  let u := min T (t + q / unfoldingScale T)
  have ht : 0 < t := (mem_cutoff.mp i.1.property).2.1
  have htu : t ≤ u := le_min (mem_cutoff.mp i.1.property).2.2
    (le_add_of_nonneg_right (div_pos hq hL).le)
  have hn := Ncount_add (a := 0) (b := t) (c := u) ht.le htu
  change discrepancy u - discrepancy t = (Ncount t u : ℝ) - (smoothCount u - smoothCount t)
  unfold discrepancy
  rw [hn, Nat.cast_add]
  ring

private theorem sampled_smooth_continuous (T : ℝ) :
    Continuous (sampledHeightIncrement smoothCount T) := by
  classical
  unfold sampledHeightIncrement
  have hs := smoothCount_continuous
  fun_prop

private theorem integral_eq_on_pos {f g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (h : ∀ q, 0 < q → f q = g q) :
    (∫ q in (0 : ℝ)..R, f q) = ∫ q in (0 : ℝ)..R, g q := by
  rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le]
  exact setIntegral_congr_fun measurableSet_Ioc (fun q hq => h q hq.1)

/-- Linear splitting holds for the actual integral, even across all the jumps
of the count process. -/
theorem cesaroSignedTrace_eq_argument_add_prime {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    cesaroSignedTrace T R = cesaroArgumentIncrement T R + primeProbeCesaroEnergy T R := by
  have hi : IntervalIntegrable
      (fun q => positiveGapMass T q - sampledHeightIncrement smoothCount T q) volume 0 R :=
    (positiveGapMass_mono hT).intervalIntegrable.sub
      ((sampled_smooth_continuous T).intervalIntegrable 0 R)
  have hB := (continuous_primeProbeEnergy_width T).intervalIntegrable (μ := volume) 0 R
  have hA := integral_eq_on_pos hR (fun q hq => sampledArgumentIncrement_eq_gap_sub_smooth hT hq)
  have hAB := integral_eq_on_pos hR (fun q hq =>
    congrArg (fun a => a + primeProbeEnergy T q) (sampledArgumentIncrement_eq_gap_sub_smooth hT hq))
  rw [cesaroSignedTrace, cesaroArgumentIncrement, primeProbeCesaroEnergy, hAB, hA,
    intervalIntegral.integral_add hi hB, mul_add]

/-- Exact signed conservation law. The raw triangle remainder and the sampled
smooth-density drift enter with their signs. -/
theorem cesaroArgument_add_collision_eq_moment_add_drift {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) :
    cesaroArgumentIncrement T R + normalizedOrdinateCollision T =
      shortWindowMomentDeficit T R + cesaroSmoothDrift T R := by
  have hA := integral_eq_on_pos hR (fun q hq => sampledArgumentIncrement_eq_gap_sub_smooth hT hq)
  have hs := (sampled_smooth_continuous T).intervalIntegrable (μ := volume) 0 R
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 R := continuous_id.intervalIntegrable _ _
  rw [cesaroArgumentIncrement, hA, intervalIntegral.integral_sub
    (positiveGapMass_mono hT).intervalIntegrable hs, cesaroSmoothDrift,
    intervalIntegral.integral_sub hi hs,
    integral_id, shortWindowMomentDeficit,
    physicalTriangle_eq_collision_add_positive_gaps hT hR.le, normalizedOrdinateCollision]
  field_simp [hR.ne']
  ring

/-- Restoring all collisions to the measured signed trace leaves precisely
the prime average and the two actual zero-count terms. -/
theorem cesaroSignedTrace_add_collision_eq {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    cesaroSignedTrace T R + normalizedOrdinateCollision T =
      primeProbeCesaroEnergy T R + shortWindowMomentDeficit T R + cesaroSmoothDrift T R := by
  rw [cesaroSignedTrace_eq_argument_add_prime hT hR]
  linarith only [cesaroArgument_add_collision_eq_moment_add_drift hT hR]

/-- Only the compensated sampled argument remains after the prime asymptotic.
At critical width its deterministic shift is exactly the diagonal mass. -/
theorem cesaroSignedTrace_centered_iff {R : ℝ → ℝ} {α : ℝ}
    (hR : Tendsto R atTop atTop)
    (hα : Tendsto (fun T : ℝ => R T / (Real.log T) ^ 2) atTop (𝓝 α)) :
    Tendsto (fun T : ℝ => cesaroSignedTrace T (R T) + normalizedOrdinateCollision T)
      atTop (𝓝 (1 + α * primeProbeDiagonal)) ↔
    Tendsto (fun T : ℝ => cesaroArgumentIncrement T (R T) + normalizedOrdinateCollision T)
      atTop (𝓝 0) := by
  have hB := primeProbeCesaroEnergy_critical hR hα
  have he : (fun T : ℝ => cesaroSignedTrace T (R T) + normalizedOrdinateCollision T) =ᶠ[atTop]
      fun T => (cesaroArgumentIncrement T (R T) + normalizedOrdinateCollision T) +
        primeProbeCesaroEnergy T (R T) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hR.eventually_gt_atTop 0] with T ht hr
    rw [cesaroSignedTrace_eq_argument_add_prime ht hr]
    ring
  constructor
  · intro h
    have hd := (h.congr' he).sub hB
    simpa only [add_sub_cancel_right, sub_self] using hd
  · intro h
    have hh := h.add hB
    exact ((by simpa only [zero_add] using hh) :
      Tendsto (fun T : ℝ => (cesaroArgumentIncrement T (R T) + normalizedOrdinateCollision T) +
        primeProbeCesaroEnergy T (R T)) atTop (𝓝 (1 + α * primeProbeDiagonal))).congr' he.symm

/-- Width contrast removes the unknown collision term at the same cutoff. -/
theorem cesaroSignedTrace_two_widths {R S : ℝ → ℝ} {α β : ℝ}
    (hR : Tendsto R atTop atTop) (hS : Tendsto S atTop atTop)
    (hα : Tendsto (fun T : ℝ => R T / (Real.log T) ^ 2) atTop (𝓝 α))
    (hβ : Tendsto (fun T : ℝ => S T / (Real.log T) ^ 2) atTop (𝓝 β))
    (ha : Tendsto (fun T : ℝ => cesaroArgumentIncrement T (R T) + normalizedOrdinateCollision T)
      atTop (𝓝 0))
    (hb : Tendsto (fun T : ℝ => cesaroArgumentIncrement T (S T) + normalizedOrdinateCollision T)
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => cesaroSignedTrace T (R T) - cesaroSignedTrace T (S T))
      atTop (𝓝 ((α - β) * primeProbeDiagonal)) := by
  have hh := ((cesaroSignedTrace_centered_iff hR hα).mpr ha).sub
    ((cesaroSignedTrace_centered_iff hS hβ).mpr hb)
  simpa only [add_sub_add_right_eq_sub, add_sub_add_left_eq_sub, sub_mul] using hh

/-- At growing submacroscopic widths, relative cancellation of the unaveraged
signed statistic is exactly the unit-density law for strict positive gaps. -/
theorem movingSignedTrace_div_width_iff_gap_density {R : ℝ → ℝ}
    (hR : Tendsto R atTop atTop)
    (hsub : Tendsto (fun T : ℝ => R T / unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ =>
      (sampledArgumentIncrement T (R T) + primeProbeEnergy T (R T)) / R T) atTop (𝓝 0) ↔
    Tendsto (fun T : ℝ => positiveGapMass T (R T) / R T) atTop (𝓝 1) := by
  have hB := primeProbeEnergy_div_width_tendsto hR
  have he := positiveGapMass_div_width_tendsto_iff_sampledArgumentIncrement
    (ℓ := 1) (hR.eventually_gt_atTop 0) hsub
  rw [sub_self] at he
  constructor
  · intro h
    apply he.mpr
    have hd := h.sub hB
    simpa only [add_div, add_sub_cancel_right, sub_zero] using hd
  · intro h
    simpa only [add_div, add_zero] using (he.mp h).add hB


/-- A signed difference of adjacent width bands, using only the same cutoff in each. -/
def dyadicSignedTraceContrast (T R : ℝ) : ℝ :=
  ((∫ q in R..(2*R), sampledArgumentIncrement T q + primeProbeEnergy T q) -
    ∫ q in (0 : ℝ)..R, sampledArgumentIncrement T q + primeProbeEnergy T q) / R

/-- The signed adjacent-band contrast is exactly a difference of two Cesàro statistics. -/
theorem dyadicSignedTraceContrast_eq {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    dyadicSignedTraceContrast T R = cesaroSignedTrace T (2 * R) - cesaroSignedTrace T R := by
  let f := fun q => sampledArgumentIncrement T q + primeProbeEnergy T q
  let g := fun q =>
    positiveGapMass T q - sampledHeightIncrement smoothCount T q + primeProbeEnergy T q
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    ((positiveGapMass_mono hT).intervalIntegrable.sub
      ((sampled_smooth_continuous T).intervalIntegrable a b)).add
        ((continuous_primeProbeEnergy_width T).intervalIntegrable a b)
  have he (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      (∫ q in a..b, f q) = ∫ q in a..b, g q := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun measurableSet_Ioc fun q hq =>
      congrArg (fun x => x + primeProbeEnergy T q)
        (sampledArgumentIncrement_eq_gap_sub_smooth hT (ha.trans_lt hq.1))
  have had := intervalIntegral.integral_add_adjacent_intervals (hg 0 R) (hg R (2 * R))
  change ((∫ q in R..(2*R), f q) - ∫ q in (0 : ℝ)..R, f q) / R =
    (2 / (2 * R)) * (∫ q in (0 : ℝ)..(2 * R), f q) - (2 / R) * ∫ q in (0 : ℝ)..R, f q
  rw [he R (2 * R) hR.le (by linarith), he 0 R le_rfl hR.le,
    he 0 (2 * R) le_rfl (by positivity), ← had]
  field_simp [hR.ne']
  ring

/-- A critical dyadic width contrast retains one copy of the diagonal shift.
Any unknown equal-ordinate mass has cancelled exactly between the two bands. -/
theorem dyadicSignedTraceContrast_critical {R : ℝ → ℝ} {α : ℝ}
    (hR : Tendsto R atTop atTop)
    (hα : Tendsto (fun T : ℝ => R T / (Real.log T) ^ 2) atTop (𝓝 α))
    (hsmall : Tendsto (fun T : ℝ => cesaroArgumentIncrement T (R T) + normalizedOrdinateCollision T)
      atTop (𝓝 0))
    (hlarge : Tendsto
      (fun T : ℝ => cesaroArgumentIncrement T (2 * R T) + normalizedOrdinateCollision T)
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => dyadicSignedTraceContrast T (R T)) atTop
      (𝓝 (α * primeProbeDiagonal)) := by
  have hR' : Tendsto (fun T : ℝ => 2 * R T) atTop atTop := hR.const_mul_atTop (by norm_num)
  have hα' : Tendsto (fun T : ℝ => (2 * R T) / (Real.log T) ^ 2) atTop (𝓝 (2 * α)) := by
    simpa only [mul_div_assoc] using hα.const_mul 2
  have hd := cesaroSignedTrace_two_widths hR' hR hα' hα hlarge hsmall
  rw [show 2 * α - α = α by ring] at hd
  refine hd.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hR.eventually_gt_atTop 0] with T ht hr
  exact (dyadicSignedTraceContrast_eq ht hr).symm



private theorem sampledSmooth_ratio_of_bounded_width {w : ℝ → ℝ} {R : ℝ}
    (hw : ∀ᶠ T : ℝ in atTop, 0 < w T)
    (hbound : ∀ᶠ T : ℝ in atTop, w T ≤ R) :
    Tendsto (fun T : ℝ => sampledHeightIncrement smoothCount T (w T) / w T) atTop (𝓝 1) := by
  have hD : Tendsto unfoldedCutoff atTop atTop :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).atTop_div_const (by positivity)
  have hupper := (tendsto_inv_atTop_zero.comp hD).const_mul R
  have hsmall : Tendsto (fun T : ℝ => w T / unfoldedCutoff T) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (by simpa only [Function.comp_def, mul_zero] using hupper)
    · filter_upwards [hw, hD.eventually_gt_atTop 0] with T ht hd
      exact div_nonneg ht.le hd.le
    · filter_upwards [hbound, hD.eventually_gt_atTop 0] with T ht hd
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right ht hd.le
  have h := (sampled_main_increment_div_width_tendsto hw hsmall).add
    (sampled_argument_comparison_tendsto hw)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [hw, eventually_gt_atTop (1 : ℝ)] with T ht hT
  have hmain := positiveGapMass_eq_sampled_main_add_RvMError hT ht
  rw [sampledArgumentIncrement_eq_gap_sub_smooth hT ht, hmain]
  ring

/-- The sampled true smooth increment has unit relative slope uniformly over
all positive widths in a fixed compact interval, including shrinking widths. -/
theorem eventually_sampledSmooth_relative_uniform {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ Ioc (0 : ℝ) R,
      |sampledHeightIncrement smoothCount T q / q - 1| ≤ ε := by
  classical
  let bad (T : ℝ) := ∃ q ∈ Ioc (0 : ℝ) R, ε < |sampledHeightIncrement smoothCount T q / q - 1|
  let w (T : ℝ) := if h : bad T then Classical.choose h else R
  have hm (T : ℝ) : w T ∈ Ioc (0 : ℝ) R := by
    dsimp only [w]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact ⟨hR, le_rfl⟩
  have hw := sampledSmooth_ratio_of_bounded_width
    (Eventually.of_forall fun T => (hm T).1) (Eventually.of_forall fun T => (hm T).2)
  have herr : Tendsto (fun T : ℝ => |sampledHeightIncrement smoothCount T (w T) / w T - 1|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hw.sub_const 1).abs
  filter_upwards [herr.eventually (gt_mem_nhds hε)] with T ht
  intro q hq
  by_contra! hn
  have hb : bad T := ⟨q,hq,hn⟩
  have hh := (Classical.choose_spec hb).2
  rw [show w T = Classical.choose hb by simp [w,hb]] at ht
  exact (not_lt_of_ge hh.le) ht

/-- The sampled smooth term contributes zero drift to the width average at
any fixed positive endpoint, without a conjecture on the zeros. -/
theorem cesaroSmoothDrift_fixed {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ => cesaroSmoothDrift T R) atTop (𝓝 0) := by
  let g (T q : ℝ) := q - sampledHeightIncrement smoothCount T q
  have hI : Tendsto (fun T : ℝ => ∫ q in (0 : ℝ)..R, g T q) atTop
      (𝓝 (∫ _ in (0 : ℝ)..R, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => R)
    · exact Eventually.of_forall fun T =>
        ((continuous_id.sub (sampled_smooth_continuous T)).aestronglyMeasurable)
    · filter_upwards [eventually_sampledSmooth_relative_uniform hR zero_lt_one] with T ht
      apply Eventually.of_forall
      intro q hq
      rw [uIoc_of_le hR.le] at hq
      have he : g T q = -q * (sampledHeightIncrement smoothCount T q / q - 1) := by
        unfold g
        field_simp [hq.1.ne']
        ring
      rw [Real.norm_eq_abs, he, abs_mul, abs_neg, abs_of_pos hq.1]
      exact (mul_le_of_le_one_right hq.1.le (ht q hq)).trans hq.2
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro q hq
      rw [uIoc_of_le hR.le] at hq
      have h := (sampledSmooth_ratio_of_bounded_width (w := fun _ => q)
        (Eventually.of_forall fun _ => hq.1) (Eventually.of_forall fun _ => hq.2)).mul_const q
      have h' : Tendsto (fun T : ℝ => sampledHeightIncrement smoothCount T q) atTop (𝓝 q) := by
        simpa only [div_mul_cancel₀ _ hq.1.ne', one_mul] using h
      simpa only [g, sub_self] using (tendsto_const_nhds (x := q)).sub h'
  simpa only [cesaroSmoothDrift, g, intervalIntegral.integral_zero, mul_zero] using
    hI.const_mul (2/R)

private theorem primeProbeCesaroEnergy_fixed {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ => primeProbeCesaroEnergy T R) atTop (𝓝 (sineHoleTriangle R)) := by
  let d := R - sineGapMass R
  have hb := (primeProbeEnergy_tendsto hR.le).eventually (gt_mem_nhds (show d < d + 1 by linarith))
  have hI : Tendsto (fun T => ∫ q in (0 : ℝ)..R, primeProbeEnergy T q) atTop
      (𝓝 (∫ q in (0 : ℝ)..R, q - sineGapMass q)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => d + 1)
    · exact Eventually.of_forall fun T => (continuous_primeProbeEnergy_width T).aestronglyMeasurable
    · filter_upwards [hb] with T ht
      apply Eventually.of_forall
      intro q hq
      rw [uIoc_of_le hR.le] at hq
      have hn : 0 ≤ primeProbeEnergy T q :=
        intervalIntegral.integral_nonneg hq.1.le fun u _ => sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact ((monotone_primeProbeEnergy_width T) hq.2).trans ht.le
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro q hq
      rw [uIoc_of_le hR.le] at hq
      exact primeProbeEnergy_tendsto hq.1.le
  have he : (2 / R) * (∫ q in (0 : ℝ)..R, q - sineGapMass q) = sineHoleTriangle R := by
    have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 R := continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi sineGapMass_mono.intervalIntegrable, integral_id,
      integral_sineGapMass, sineHoleTriangle]
    ring
  simpa only [primeProbeCesaroEnergy, he] using hI.const_mul (2/R)

/-- At a fixed positive endpoint the two signed primitives cancel exactly in
the limit without any zero-pair limit assumption. -/
theorem cesaroSignedTrace_add_gapDeficit_fixed {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ => cesaroSignedTrace T R + integratedGapDeficit T R) atTop (𝓝 0) := by
  have h := ((primeProbeCesaroEnergy_fixed hR).sub_const (sineHoleTriangle R)).add
    (cesaroSmoothDrift_fixed hR)
  simp only [sub_self, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hc := collision_div_main_eq_signed_gap_deficits hT hR
  change normalizedOrdinateCollision T = _ at hc
  linarith only [hc, cesaroSignedTrace_add_collision_eq hT hR]

/-- Initial width averages at the positive rationals suffice to recover all
fixed-width, ordinary positive-gap pair correlation. -/
theorem positiveGapPCC_iff_rationalCesaroSignedTrace :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => cesaroSignedTrace T q) atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_rationalIntegratedGapDeficit]
  constructor <;> intro h q hq
  · have hd := (cesaroSignedTrace_add_gapDeficit_fixed (R := q) (by exact_mod_cast hq)).sub (h q hq)
    simpa only [add_sub_cancel_right, sub_zero] using hd
  · have hd := (cesaroSignedTrace_add_gapDeficit_fixed (R := q) (by exact_mod_cast hq)).sub (h q hq)
    simpa only [add_sub_cancel_left, sub_zero] using hd

/-- Uniform transfer on compact width intervals all the way down to the origin:
the full signed trace and the actual strict-gap discrepancy have the same
microscopic limits, even along arbitrarily varying bounded positive widths. -/
theorem eventually_signedTrace_gap_error_uniform {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ Ioc (0 : ℝ) R,
      |(sampledArgumentIncrement T q + primeProbeEnergy T q) -
        (positiveGapMass T q - sineGapMass q)| ≤ ε := by
  obtain ⟨K,hK,hbound⟩ := primeProbeEnergyExcess_uniform
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hu : Tendsto (fun T : ℝ => K * (1 / Real.log T + R / (Real.log T)^2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
      using (hi.add ((hi.pow 2).const_mul R)).const_mul K
  have hhalf : 0 < ε/2 := by positivity
  have htol : 0 < ε/(2*R) := by positivity
  filter_upwards [hu.eventually (gt_mem_nhds hhalf), eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_sampledSmooth_relative_uniform hR htol]
      with T hprime hT hL hs
  intro q hq
  have he := (hbound hT hL hq.1.le).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (div_le_div_of_nonneg_right hq.2 (sq_nonneg _))) hK.le)
  have hsm : |q - sampledHeightIncrement smoothCount T q| ≤ ε/2 := by
    rw [show q - sampledHeightIncrement smoothCount T q =
      -q * (sampledHeightIncrement smoothCount T q / q - 1) by
        field_simp [hq.1.ne']
        ring,
      abs_mul, abs_neg, abs_of_pos hq.1]
    calc
      _ ≤ q * (ε/(2*R)) := mul_le_mul_of_nonneg_left (hs q hq) hq.1.le
      _ ≤ R * (ε/(2*R)) := mul_le_mul_of_nonneg_right hq.2 htol.le
      _ = ε/2 := by field_simp [hR.ne']
  have hid : sampledArgumentIncrement T q + primeProbeEnergy T q -
      (positiveGapMass T q - sineGapMass q) = primeProbeEnergyExcess T q +
        (q - sampledHeightIncrement smoothCount T q) := by
    rw [sampledArgumentIncrement_eq_gap_sub_smooth hT hq.1, primeProbeEnergyExcess]; ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [he, hsm, hprime])



/-- The M17 error is negligible even at the scale of the smooth sampled
height bias, for every diverging probe width. -/
theorem primeProbeEnergyExcess_div_smooth_scale {R : ℝ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun T : ℝ => (Real.log T/R T)*primeProbeEnergyExcess T (R T))
      atTop (𝓝 0) := by
  obtain ⟨K,hK,he⟩ := primeProbeEnergyExcess_uniform
  have hr := hR.const_div_atTop (1:ℝ)
  have hl := Real.tendsto_log_atTop.const_div_atTop (1:ℝ)
  have hz : Tendsto (fun T : ℝ => K*(1/R T+1/Real.log T)) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hr.add hl).const_mul K
  apply squeeze_zero_norm' _ hz
  filter_upwards [hR.eventually_gt_atTop 0, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with T hRT hT hL
  have hlog := Real.log_pos hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hlog hRT)]
  apply (mul_le_mul_of_nonneg_left (he hT hL hRT.le) (div_pos hlog hRT).le).trans_eq
  field_simp [hRT.ne',hlog.ne']

/-- On every growing submacroscopic width the signed prime–zero trace has a
deterministic second-order displacement from the strict-gap discrepancy.
The clipping parabola is kept exactly, also when it dominates the logarithmic term. -/
theorem movingSignedTrace_gap_logarithmic_drift {R : ℝ → ℝ}
    (hR : Tendsto R atTop atTop)
    (hs : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (Real.log T/R T)*
      ((sampledArgumentIncrement T (R T)+primeProbeEnergy T (R T)) -
       (positiveGapMass T (R T)-sineGapMass (R T))-(R T)^2/(2*unfoldedCutoff T)))
      atTop (𝓝 (2*(1+Real.log (2*Real.pi)))) := by
  have hmain := positiveGapMass_sub_sampledArgument_logarithmic_drift (r:=1)
    zero_lt_one (hR.eventually_ge_atTop _) hs
  have h := (primeProbeEnergyExcess_div_smooth_scale hR).sub hmain
  simp only [zero_sub,neg_mul,neg_neg] at h
  apply h.congr'
  filter_upwards [hR.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T hRT hT
  have hD : 0 < unfoldedCutoff T := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT))
    (by positivity)
  change (Real.log T/R T)*primeProbeEnergyExcess T (R T) - Real.log T *
    ((positiveGapMass T (R T)-sampledArgumentIncrement T (R T))/R T -
      (1-R T/(2*unfoldedCutoff T))) = _
  unfold primeProbeEnergyExcess
  field_simp [hRT.ne',hD.ne']
  ring

/-- At logarithmic width the signed trace differs from the actual strict-gap
discrepancy by a finite, explicit smooth bias. -/
theorem movingSignedTrace_gap_log_width {R : ℝ → ℝ} {ell : ℝ}
    (hR : Tendsto R atTop atTop)
    (hell : Tendsto (fun T : ℝ => R T/Real.log T) atTop (𝓝 ell)) :
    Tendsto (fun T : ℝ => (sampledArgumentIncrement T (R T)+primeProbeEnergy T (R T)) -
      (positiveGapMass T (R T)-sineGapMass (R T))) atTop
      (𝓝 (ell*(2*(1+Real.log (2*Real.pi))))) := by
  have hs : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0) := by
    have h := hell.mul (tendsto_id.const_div_atTop (2*Real.pi : ℝ))
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    change R T/Real.log T * (2*Real.pi/T) = R T/unfoldedCutoff T
    unfold unfoldedCutoff
    field_simp [(zero_lt_one.trans ht).ne', (Real.log_pos ht).ne', Real.pi_ne_zero]
  have hclip : Tendsto (fun T : ℝ => (R T)^2/(2*unfoldedCutoff T)) atTop (𝓝 0) := by
    have h := (hell.pow 2).mul (Real.log_div_self_tendsto_zero.const_mul Real.pi)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    unfold unfoldedCutoff
    field_simp [(Real.log_pos ht).ne', (zero_lt_one.trans ht).ne', Real.pi_ne_zero]
    <;> ring
  have h := (hell.mul (movingSignedTrace_gap_logarithmic_drift hR hs)).add hclip
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [hR.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T hr ht
  have hratio : R T/Real.log T * (Real.log T/R T) = 1 := by
    field_simp [hr.ne',(Real.log_pos ht).ne']
  rw [←mul_assoc, hratio, one_mul, sub_add_cancel]

/-- info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.positiveGapPCC_iff_rationalCesaroSignedTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_rationalCesaroSignedTrace

/-- info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.movingSignedTrace_gap_logarithmic_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms movingSignedTrace_gap_logarithmic_drift

/-- info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.dyadicSignedTraceContrast_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyadicSignedTraceContrast_critical

/-- info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.eventually_signedTrace_gap_error_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_signedTrace_gap_error_uniform

end RiemannResearch.Analysis.MontgomeryPrimeTrace
