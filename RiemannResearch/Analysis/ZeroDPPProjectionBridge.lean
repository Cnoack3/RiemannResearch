import RiemannResearch.Analysis.ZeroDPPProjectedDistinctSpacing
import RiemannResearch.Analysis.ZeroDPPCollisionLoss
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion

/-! Width-integrated decomposition for the prime-frequency projection and the
ordinary occurrence measure. Self-pairs occur exactly once in the restored statistic.
The deleted term retains distinct labels at equal coordinates. -/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZeroDPPProjectionBridge
open ActualZeroOrdinate ActualZeroCollisionCertificate
open ActualZeroWindowVariance MontgomeryPositiveGap
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open ProjectedDistinctSpacing ZeroDPPCollisionLoss ProjectionDPP

private theorem integral_above {k a b : ℝ} (ha : k ≤ a) (hab : a ≤ b) :
    (∫ r in a..b, max (r-k) 0) = ((b-k)^2-(a-k)^2)/2 := by
  have e : (∫ r in a..b, max (r-k) 0) = ∫ r in a..b, r-k := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro r hr
    exact max_eq_left (sub_nonneg.mpr (ha.trans hr.1))
  rw [e, intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => k)
    (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem integral_below {k a b : ℝ} (hab : a ≤ b) (hb : b ≤ k) :
    (∫ r in a..b, max (r-k) 0) = 0 := by
  calc
    _ = ∫ _ in a..b, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hab]
      intro r hr
      exact max_eq_right (sub_nonpos.mpr (hr.2.trans hb))
    _ = _ := by simp

theorem integratedTriangle_eq_widthProbe {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    integratedTriangle a b u = widthProbe a b u := by
  unfold integratedTriangle widthProbe
  rcases le_total b |u| with hb | hb
  · rw [integral_below hab hb, max_eq_right (sub_nonpos.mpr hb),
      max_eq_right (sub_nonpos.mpr (hab.trans hb))]; norm_num
  rcases le_total |u| a with ha | ha
  · rw [max_eq_left (sub_nonneg.mpr hb), max_eq_left (sub_nonneg.mpr ha),
      integral_above ha hab]
  have hc : Continuous (fun r : ℝ => max (r-|u|) 0) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a |u|) (hc.intervalIntegrable |u| b),
    integral_below ha le_rfl, integral_above le_rfl hb,
    max_eq_left (sub_nonneg.mpr hb), max_eq_right (sub_nonpos.mpr ha)]
  ring

private theorem rescale_entry {L : ℝ} (hL : 0 < L) (r d : ℝ) :
    max (r/L - |d|) 0 = max (r - |L*d|) 0 / L := by
  rw [abs_mul, abs_of_pos hL]
  have e : (r-L*|d|)/L = r/L-|d| := by field_simp
  rcases le_total (r-L*|d|) 0 with h | h
  · rw [max_eq_right h, zero_div, max_eq_right]
    rw [← e]; exact div_nonpos_of_nonpos_of_nonneg h hL.le
  · rw [max_eq_left h, e, max_eq_left]
    rw [← e]; exact div_nonneg h hL.le

private theorem integral_unfolded_eq_sum {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    (∫ r in a..b, unfoldedWindowEnergy T r) =
      ∑ i : Copies T, ∑ j : Copies T,
        unfoldedProbe T a b (copyOrdinate T i) (copyOrdinate T j) := by
  let L := Real.log T / (2*Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  let w := fun (i j : Copies T) (r : ℝ) =>
    max (r - |L*(copyOrdinate T i - copyOrdinate T j)|) 0 / normalizer T
  have hc (i j : Copies T) : Continuous (w i j) := by dsimp [w]; fun_prop
  have he (r : ℝ) : unfoldedWindowEnergy T r = ∑ i : Copies T, ∑ j : Copies T, w i j r := by
    unfold unfoldedWindowEnergy actualPhysicalTriangleEnergy
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change max (r/L - |copyOrdinate T i - copyOrdinate T j|) 0 / T = _
    rw [rescale_entry hL]
    dsimp [w, L, normalizer]
    field_simp [Real.pi_ne_zero, (Real.log_pos hT).ne', (zero_lt_one.trans hT).ne']
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (f := fun i r => ∑ j : Copies T, w i j r)
    (fun i _ => (continuous_finsetSum _ fun j _ => hc i j).intervalIntegrable a b)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (f := fun j r => w i j r)
    (fun j _ => (hc i j).intervalIntegrable a b)]
  apply Finset.sum_congr rfl
  intro j _
  change (∫ r in a..b, max (r-|L*(copyOrdinate T i-copyOrdinate T j)|) 0 / normalizer T) = _
  rw [intervalIntegral.integral_div]
  exact congrArg (fun s : ℝ => s / normalizer T) (integratedTriangle_eq_widthProbe hab _)

theorem actual_integral_eq_restored_add_loss {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    (∫ r in a..b, unfoldedWindowEnergy T r) =
      restoredPrimeMoment T a b + triangleLoss primeFrequencies T a b := by
  classical
  rw [integral_unfolded_eq_sum hT hab]
  let w := fun i j : Copies T => unfoldedProbe T a b (copyOrdinate T i) (copyOrdinate T j)
  let k := fun i j : Copies T => limitingKernel primeFrequencies (liftCopy T i) (liftCopy T j)
  let p := fun i j : Copies T => k i i * k j j - k i j * k j i
  have kept {i j : Copies T} (h : i ≠ j) : keptPair primeFrequencies T i j = p i j := by
    rw [keptPair, limitingLaw_two_point _ ((liftCopy T).injective.ne h)]
    dsimp [p, k]
    have hs : limitingKernel primeFrequencies (liftCopy T j) (liftCopy T i) =
       limitingKernel primeFrequencies (liftCopy T i) (liftCopy T j) := kernel_symmetric _ _ _ _
    rw [hs, pow_two]
  have hl : triangleLoss primeFrequencies T a b =
      ∑ i, ∑ j, if i = j then 0 else w i j * (1 - p i j) := by
    unfold triangleLoss
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j
    · simp [h]
    · simp only [h, if_false, integratedTriangle_eq_widthProbe hab, kept h]
      dsimp [w, unfoldedProbe, normalizer]; ring
  rw [hl]
  change (∑ i, ∑ j, w i j) = (∑ i, w i i) + (∑ i, ∑ j, w i j * p i j) +
    ∑ i, ∑ j, if i = j then 0 else w i j * (1 - p i j)
  calc
    _ = ∑ i, ∑ j, ((if j = i then w i i else 0) + w i j * p i j +
        (if i = j then 0 else w i j * (1 - p i j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · subst j; simp [p]
      · simp only [h, Ne.symm h, if_false]; ring
    _ = _ := by simp [Finset.sum_add_distrib]

/-- At fixed width endpoints a vanishing deletion term gives an equivalence of
the two limits, including the reverse transfer from the full occurrence statistic. -/
theorem restored_tendsto_iff_actual_of_loss {a b c : ℝ} (hab : a ≤ b)
    (h : Tendsto (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => restoredPrimeMoment T a b) atTop (𝓝 c) ↔
    Tendsto (fun T : ℝ => ∫ r in a..b, unfoldedWindowEnergy T r) atTop (𝓝 c) := by
  constructor
  · intro hp
    have hs := hp.add h
    rw [add_zero] at hs
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    exact (actual_integral_eq_restored_add_loss ht hab).symm
  · intro hf
    have hs := hf.sub h
    rw [sub_zero] at hs
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    change (∫ r in a..b, unfoldedWindowEnergy T r) - triangleLoss primeFrequencies T a b = _
    rw [actual_integral_eq_restored_add_loss ht hab, add_sub_cancel_right]

/-- Width-averaged sine prediction for the unweighted prime projection, with every
occurrence-label self-pair restored. -/
def PrimeProjectedSineLimit : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → Tendsto (fun T : ℝ => restoredPrimeMoment T a b)
    atTop (𝓝 (∫ r in (a : ℝ)..(b : ℝ), sineWindowEnergy r))

theorem positiveGapPCC_of_prime_loss_and_restored
    (hloss : ∀ a b : ℚ, 0 < a → a < b → Tendsto
      (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0))
    (hp : PrimeProjectedSineLimit) : PositiveGapPCC := by
  apply positiveGapPCC_of_rationalTriangleWidthAverages
  intro a b ha hab
  have h := (hp a b ha hab).add (hloss a b ha hab)
  rw [add_zero] at h
  have hz := h.sub (tendsto_const_nhds (x := ∫ r in (a:ℝ)..(b:ℝ), sineWindowEnergy r))
  rw [sub_self] at hz
  refine hz.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  rw [intervalIntegral.integral_sub (unfoldedWindowEnergy_mono T hT).intervalIntegrable
    (continuous_sineWindowEnergy.intervalIntegrable _ _)]
  rw [actual_integral_eq_restored_add_loss hT (by exact_mod_cast hab.le)]
end RiemannResearch.Analysis.ZeroDPPProjectionBridge
