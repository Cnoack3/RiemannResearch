import RiemannResearch.RH.ProjectedDualProjectionError
import RiemannResearch.RH.ResidueCorrectionAbel

/-!
# Certified finite shells for the actual inverse-Gram correction

Source: `AnthropicRHBridges20260928.md`, section 3, supplied by the user
on 28 September 2026. The cutoff below accepts any certified upper bound
for the complete arithmetic tail energy. The unconditional linear
majorant gives an explicit cutoff without an arithmetic growth hypothesis.
This is an analytic accuracy certificate; it does not assert an efficient
numerical algorithm.

The finite signed shell can be rewritten by either exact Abel formula.
All absolute values below are taken after forming that signed shell.
The cofinal smallness hypothesis in the final theorem remains open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open GramMobiusCorrection

/-- The actual finite physical shell, before any absolute-value estimate. -/
def correctionShellValue (n d M : ℕ) : ℝ :=
  hilbertShellPairing ((finiteSpace n).starProjection (coefficientRiesz d))
    (tailError n) n M

theorem correctionShellValue_eq_abel (n d M : ℕ) :
    correctionShellValue n d M = correctionAbelValue n d M :=
  correction_shell_abel n d M

theorem correctionShellValue_eq_abel_second (n d M : ℕ) :
    correctionShellValue n d M = correctionAbelSecondValue n d M :=
  correction_shell_abel_second n d M

private theorem cutoff_tail_energy_le (f : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailShift f N‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hs := hilbertTailShift_norm_sq f N
  have hsum : 0 ≤ ∑ k ∈ Finset.range N, (f k) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- The complete omitted tail, bounded without truncating either factor. -/
theorem correction_sub_shell_sq_le (n d M : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - correctionShellValue n d M| ^ 2 ≤
      projectedDualCoefficientMass n d ^ 2 * ‖tailError n‖ ^ 2 /
        ((n + M : ℕ) + 1 : ℝ) := by
  let u := hilbertTailShift
    ((finiteSpace n).starProjection (coefficientRiesz d)) (n + M)
  let v := hilbertTailShift (tailError n) (n + M)
  have he : correction n d - correctionShellValue n d M = inner ℝ u v := by
    have hs := correction_signed_shell_split n d M hd hdn
    change correction n d = correctionShellValue n d M + inner ℝ u v at hs
    linarith
  have hu : ‖u‖ ^ 2 ≤ projectedDualCoefficientMass n d ^ 2 /
      ((n + M : ℕ) + 1 : ℝ) :=
    projectedDualTail_any_cutoff_le_mass n d (n + M)
  have hv : ‖v‖ ^ 2 ≤ ‖tailError n‖ ^ 2 := cutoff_tail_energy_le _ _
  rw [he]
  calc
    |inner ℝ u v| ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (abs_real_inner_le_norm u v)
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ ≤ (projectedDualCoefficientMass n d ^ 2 /
        ((n + M : ℕ) + 1 : ℝ)) * ‖tailError n‖ ^ 2 :=
      mul_le_mul hu hv (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- A cutoff computed from an arbitrary certified energy majorant. -/
def correctionCutoffWithEnergy (n d : ℕ) (E : ℝ) : ℕ :=
  ⌈((n : ℝ) + 1) * projectedDualCoefficientMass n d ^ 2 * E⌉₊

/-- An energy upper bound gives a finite shell with squared error at most
`1 / (n+1)`. No upper bound on the inverse-column mass is required. -/
theorem correction_sub_shell_sq_le_of_cutoffWithEnergy_le (n d M : ℕ) (E : ℝ)
    (hd : 1 < d) (hdn : d ≤ n) (hE : ‖tailError n‖ ^ 2 ≤ E)
    (hM : correctionCutoffWithEnergy n d E ≤ M) :
    |correction n d - correctionShellValue n d M| ^ 2 ≤
        1 / ((n : ℝ) + 1) := by
  have hceil : ((n : ℝ) + 1) * projectedDualCoefficientMass n d ^ 2 * E ≤
      (correctionCutoffWithEnergy n d E : ℝ) := Nat.le_ceil _
  have hMR : (correctionCutoffWithEnergy n d E : ℝ) ≤ M := by exact_mod_cast hM
  calc
    _ ≤ projectedDualCoefficientMass n d ^ 2 * ‖tailError n‖ ^ 2 /
        ((n + M : ℕ) + 1 : ℝ) :=
      correction_sub_shell_sq_le n d _ hd hdn
    _ ≤ projectedDualCoefficientMass n d ^ 2 * E /
        ((n + M : ℕ) + 1 : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)
    _ ≤ 1 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      push_cast
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

theorem correction_sub_cutoffWithEnergy_sq_le (n d : ℕ) (E : ℝ)
    (hd : 1 < d) (hdn : d ≤ n) (hE : ‖tailError n‖ ^ 2 ≤ E) :
    |correction n d -
      correctionShellValue n d (correctionCutoffWithEnergy n d E)| ^ 2 ≤
        1 / ((n : ℝ) + 1) :=
  correction_sub_shell_sq_le_of_cutoffWithEnergy_le n d _ E hd hdn hE le_rfl

/-- A coarse unconditional upper bound for the complete arithmetic energy. -/
theorem tailError_energy_le_linear (n : ℕ) (hn : 0 < n) :
    ‖tailError n‖ ^ 2 ≤ 8 * (n : ℝ) + 2 := by
  have hres := canonicalMobiusResidual_norm_sq_le n
  have hcan := canonicalMobiusHilbert_norm_sq_lt_four_mul n hn
  change ‖hilbertOne - canonicalMobiusHilbert n‖ ^ 2 ≤ _
  nlinarith

/-- The unconditional finite cutoff obtained from the linear energy bound. -/
def correctionCertifiedCutoff (n d : ℕ) : ℕ :=
  correctionCutoffWithEnergy n d (8 * (n : ℝ) + 2)

/-- The certified finite signed value. -/
def correctionCertifiedValue (n d : ℕ) : ℝ :=
  correctionShellValue n d (correctionCertifiedCutoff n d)

theorem correction_sub_certified_sq_le (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - correctionCertifiedValue n d| ^ 2 ≤
      1 / ((n : ℝ) + 1) :=
  correction_sub_cutoffWithEnergy_sq_le n d _ hd hdn
    (tailError_energy_le_linear n (by omega))

/-- Every later shell retains the same accuracy certificate. -/
theorem correction_sub_shell_sq_le_of_certified_le (n d M : ℕ)
    (hd : 1 < d) (hdn : d ≤ n) (hM : correctionCertifiedCutoff n d ≤ M) :
    |correction n d - correctionShellValue n d M| ^ 2 ≤
      1 / ((n : ℝ) + 1) :=
  correction_sub_shell_sq_le_of_cutoffWithEnergy_le n d M _ hd hdn
    (tailError_energy_le_linear n (by omega)) hM

/-- Arbitrarily enlarged certified shells have vanishing approximation error. -/
theorem correction_sub_shellSequence_tendsto_zero (d : ℕ) (hd : 1 < d)
    (M : ℕ → ℕ) (hM : ∀ᶠ n : ℕ in atTop, correctionCertifiedCutoff n d ≤ M n) :
    Tendsto (fun n => correction n d - correctionShellValue n d (M n))
      atTop (𝓝 0) := by
  have hrate : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε ^ 2 :=
    hrate.eventually_lt_const (sq_pos_of_pos hε)
  filter_upwards [hsmall, eventually_ge_atTop d, hM] with n hn hdn hMn
  rw [Real.dist_eq, sub_zero]
  have hb := correction_sub_shell_sq_le_of_certified_le n d (M n) hd hdn hMn
  have habs := abs_nonneg (correction n d - correctionShellValue n d (M n))
  nlinarith

/-- The certified finite approximation error vanishes for each old coordinate. -/
theorem correction_sub_certified_tendsto_zero (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => correction n d - correctionCertifiedValue n d)
      atTop (𝓝 0) :=
  correction_sub_shellSequence_tendsto_zero d hd (fun n => correctionCertifiedCutoff n d)
    (Eventually.of_forall (fun _ => le_rfl))

theorem correctionShellSequence_tendsto (d : ℕ) (hd : 1 < d)
    (M : ℕ → ℕ) (hM : ∀ᶠ n : ℕ in atTop, correctionCertifiedCutoff n d ≤ M n) :
    Tendsto (fun n => correctionShellValue n d (M n)) atTop
      (𝓝 (mobiusDifferenceCLM d limitResidual)) := by
  have h := (correction_tendsto_residual d (by omega)).sub
    (correction_sub_shellSequence_tendsto_zero d hd M hM)
  simpa only [sub_zero, sub_sub_cancel] using h

/-- The finite signed values converge to the existing correction limit,
which has not been shown to vanish. -/
theorem correctionCertifiedValue_tendsto (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => correctionCertifiedValue n d) atTop
      (𝓝 (mobiusDifferenceCLM d limitResidual)) := by
  have h := (correction_tendsto_residual d (by omega)).sub
    (correction_sub_certified_tendsto_zero d hd)
  simpa only [sub_zero, sub_sub_cancel] using h

/-- Cofinal smallness of finite signed values forces the fixed correction
limit to vanish. The smallness premise is the arithmetic obligation. -/
theorem cofinal_certified_forces_limit (d : ℕ) (hd : 1 < d)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |correctionCertifiedValue n d| < ε) :
    mobiusDifferenceCLM d limitResidual = 0 := by
  let L := mobiusDifferenceCLM d limitResidual
  by_contra hne
  have hpos : 0 < |L| / 2 := by have := abs_pos.mpr hne; positivity
  have hlarge : ∀ᶠ n : ℕ in atTop,
      |L| / 2 < |correctionCertifiedValue n d| :=
    (correctionCertifiedValue_tendsto d hd).abs.eventually_const_lt (by
      change |L| / 2 < |L|
      linarith [abs_pos.mpr hne])
  obtain ⟨n, hn, hn'⟩ := ((hsmall (|L| / 2) hpos).and_eventually hlarge).exists
  linarith

/-- CONDITIONAL RESEARCH REDUCTION: separate cofinal cancellation of the
finite signed shell for each coordinate implies RH. -/
theorem riemannHypothesis_of_cofinal_certified
    (hsmall : ∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |correctionCertifiedValue n d| < ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_correction_limits
  intro d hd
  have hz := cofinal_certified_forces_limit d hd (hsmall d hd)
  simpa only [hz] using correction_tendsto_residual d (by omega)

/-- Enlarge the certified cutoff so the terminal physical index is a
multiple of every conductor in the stage-n legal space. -/
def correctionPeriodCutoff (n d : ℕ) : ℕ :=
  (n + 1).factorial * (correctionCertifiedCutoff n d + (n + 1)) - (n + 1)

theorem correctionCertifiedCutoff_le_period (n d : ℕ) :
    correctionCertifiedCutoff n d ≤ correctionPeriodCutoff n d := by
  have hf : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
  have hmul : correctionCertifiedCutoff n d + (n + 1) ≤
      (n + 1).factorial * (correctionCertifiedCutoff n d + (n + 1)) := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (correctionCertifiedCutoff n d + (n + 1)) hf
  unfold correctionPeriodCutoff
  omega

theorem correctionPeriodCutoff_endpoint (n d : ℕ) :
    n + 1 + correctionPeriodCutoff n d =
      (n + 1).factorial * (correctionCertifiedCutoff n d + (n + 1)) := by
  have hf : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
  have hmul : correctionCertifiedCutoff n d + (n + 1) ≤
      (n + 1).factorial * (correctionCertifiedCutoff n d + (n + 1)) := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (correctionCertifiedCutoff n d + (n + 1)) hf
  have hp : n + 1 ≤
      (n + 1).factorial * (correctionCertifiedCutoff n d + (n + 1)) := by
    omega
  unfold correctionPeriodCutoff
  omega

theorem correctionPeriodCutoff_endpoint_dvd (n d : ℕ) :
    (n + 1).factorial ∣ n + 1 + correctionPeriodCutoff n d := by
  rw [correctionPeriodCutoff_endpoint]
  exact ⟨_, rfl⟩

/-- The period-aligned finite signed value. Its Abel boundary term vanishes. -/
def correctionPeriodValue (n d : ℕ) : ℝ :=
  correctionShellValue n d (correctionPeriodCutoff n d)

theorem correction_sub_period_sq_le (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - correctionPeriodValue n d| ^ 2 ≤
      1 / ((n : ℝ) + 1) :=
  correction_sub_shell_sq_le_of_certified_le n d _ hd hdn
    (correctionCertifiedCutoff_le_period n d)

theorem correction_sub_period_tendsto_zero (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => correction n d - correctionPeriodValue n d)
      atTop (𝓝 0) :=
  correction_sub_shellSequence_tendsto_zero d hd (fun n => correctionPeriodCutoff n d)
    (Eventually.of_forall (fun n => correctionCertifiedCutoff_le_period n d))

theorem correctionPeriodValue_tendsto (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => correctionPeriodValue n d) atTop
      (𝓝 (mobiusDifferenceCLM d limitResidual)) :=
  correctionShellSequence_tendsto d hd (fun n => correctionPeriodCutoff n d)
    (Eventually.of_forall (fun n => correctionCertifiedCutoff_le_period n d))

theorem cofinal_period_forces_limit (d : ℕ) (hd : 1 < d)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |correctionPeriodValue n d| < ε) :
    mobiusDifferenceCLM d limitResidual = 0 := by
  let L := mobiusDifferenceCLM d limitResidual
  by_contra hne
  have hpos : 0 < |L| / 2 := by have := abs_pos.mpr hne; positivity
  have hlarge : ∀ᶠ n : ℕ in atTop,
      |L| / 2 < |correctionPeriodValue n d| :=
    (correctionPeriodValue_tendsto d hd).abs.eventually_const_lt (by
      change |L| / 2 < |L|
      linarith [abs_pos.mpr hne])
  obtain ⟨n, hn, hn'⟩ := ((hsmall (|L| / 2) hpos).and_eventually hlarge).exists
  linarith

/-- CONDITIONAL RESEARCH REDUCTION: cofinal cancellation at aligned finite
cutoffs implies RH, with no hypothesis on inverse-column mass growth. -/
theorem riemannHypothesis_of_cofinal_period
    (hsmall : ∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |correctionPeriodValue n d| < ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_correction_limits
  intro d hd
  have hz := cofinal_period_forces_limit d hd (hsmall d hd)
  simpa only [hz] using correction_tendsto_residual d (by omega)

/-! ## Principal declaration names from the supplied markdown -/


/-- The complete projected-dual tail at any later cutoff, in the manuscript's
notation. The estimate does not require a growth bound on column mass. -/
theorem projectedDual_later_tail_energy_bound (n d K : ℕ) :
    ‖hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) K‖ ^ 2 ≤
      projectedDualCoefficientMass n d ^ 2 / ((K : ℝ) + 1) :=
  projectedDualTail_any_cutoff_le_mass n d K

/-- The complete truncation estimate with the signed second Abel expression. -/
theorem correction_sub_abel_sq_le (n d M : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - correctionAbelSecondValue n d M| ^ 2 ≤
      projectedDualCoefficientMass n d ^ 2 * ‖tailError n‖ ^ 2 /
        ((n + M : ℕ) + 1 : ℝ) := by
  simpa only [correctionShellValue_eq_abel_second] using
    correction_sub_shell_sq_le n d M hd hdn

/-- The same estimate with the first Abel expression. -/
theorem correction_sub_abel_first_sq_le (n d M : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - correctionAbelValue n d M| ^ 2 ≤
      projectedDualCoefficientMass n d ^ 2 * ‖tailError n‖ ^ 2 /
        ((n + M : ℕ) + 1 : ℝ) := by
  simpa only [correctionShellValue_eq_abel] using
    correction_sub_shell_sq_le n d M hd hdn

/-- The explicit cutoff from the manuscript, with energy majorant `8n+2`. -/
def abelCutoff (n d : ℕ) : ℕ := correctionCertifiedCutoff n d

/-- The actual second Abel value at the explicit certified cutoff. -/
def abelCutoffValue (n d : ℕ) : ℝ :=
  correctionAbelSecondValue n d (abelCutoff n d)

theorem correctionCertifiedValue_eq_abelCutoffValue (n d : ℕ) :
    correctionCertifiedValue n d = abelCutoffValue n d :=
  correctionShellValue_eq_abel_second n d (correctionCertifiedCutoff n d)

/-- The manuscript's explicit finite accuracy certificate. -/
theorem correction_sub_abelCutoff_sq_le (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - abelCutoffValue n d| ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  simpa only [correctionCertifiedValue_eq_abelCutoffValue] using
    correction_sub_certified_sq_le n d hd hdn

theorem correction_sub_abelCutoff_tendsto_zero (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => correction n d - abelCutoffValue n d) atTop (𝓝 0) := by
  simpa only [correctionCertifiedValue_eq_abelCutoffValue] using
    correction_sub_certified_tendsto_zero d hd

/-- The limit exists unconditionally; the theorem does not assert it is zero. -/
theorem abelCutoff_value_tendsto (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => abelCutoffValue n d) atTop
      (𝓝 (mobiusDifferenceCLM d limitResidual)) := by
  simpa only [correctionCertifiedValue_eq_abelCutoffValue] using
    correctionCertifiedValue_tendsto d hd

/-- CONDITIONAL RESEARCH REDUCTION: the manuscript's cofinal cancellation
condition, applied to the actual signed second Abel expression, implies RH. -/
theorem riemannHypothesis_of_cofinal_abelCutoff
    (hsmall : ∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |abelCutoffValue n d| < ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_certified
  simpa only [correctionCertifiedValue_eq_abelCutoffValue] using hsmall

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
