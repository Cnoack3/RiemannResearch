import RiemannResearch.RH.NaturalMobiusDerivativeConvergence
import RiemannResearch.RH.DerivativeAdjointRows
import RiemannResearch.Analysis.SignedAbel

/-!
# Fixed signed derivative corrections and dimension-independent limit control

Source: user-directed continuation from commit 41b7faf6, assembling
NaturalMobiusDerivativeConvergence, DerivativeAdjointRows, and the existing
Analysis/SignedAbel finite identities. No novelty claim is made.

All estimates concern the error ABOUT the identified correction limit.
Vanishing of that limit remains an explicit arithmetic obligation.
The exact vector square and both Abel boundary terms are retained.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open GramMobiusCorrection
open RiemannResearch.Analysis.SignedAbel

/-- The full signed row of the original inverse-Gram correction. -/
def signedCorrectionRow (n i : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j *
    inner ℝ (derivativeAtom i) (derivativeAtom j.val)

theorem signedCorrectionRow_eq_pairing (n i : ℕ) :
    signedCorrectionRow n i =
      inner ℝ (derivativeAtom i) (hilbertDifference (correctionSynthesis n)) := by
  rw [derivative_correction_synthesis, Fintype.linearCombination_apply, inner_sum]
  simp only [signedCorrectionRow, real_inner_smul_right, derivativeFamily]

theorem fixedMismatch_eq_raw_sub_signedCorrectionRow (n i : ℕ) :
    fixedMismatch n i =
      inner ℝ (derivativeAtom i) (rawMobiusDerivativeResidual (n + 1)) -
        signedCorrectionRow n i := by
  rw [signedCorrectionRow_eq_pairing]
  exact fixedMismatch_eq_raw_sub_correctionSynthesis n i

theorem signedCorrectionRow_tendsto (i : ℕ) :
    Tendsto (fun n => signedCorrectionRow n i) atTop
      (𝓝 (-inner ℝ limitResidual (derivativeAdjointRow i))) := by
  have h := ((innerSL ℝ (derivativeAtom i)).continuous.tendsto _).comp
    derivative_correction_tendsto
  change Tendsto (fun n => inner ℝ (derivativeAtom i)
    (hilbertDifference (correctionSynthesis n))) atTop
    (𝓝 (inner ℝ (derivativeAtom i) (-hilbertDifference limitResidual))) at h
  simpa only [← signedCorrectionRow_eq_pairing, inner_neg_right,
    fixedMismatch_limit_eq_adjoint_pairing] using h

/-- Exact error vector relative to the possibly nonzero limit. -/
theorem correction_limit_error_exact (n : ℕ) :
    hilbertDifference (correctionSynthesis n) + hilbertDifference limitResidual =
      rawMobiusDerivativeResidual (n + 1) -
        hilbertDifference (limitProjection - projection n) := by
  rw [derivative_correction_exact, derivativeResidual, limitResidual, map_sub, map_sub, map_sub]
  abel

/-- All signed cross terms and both square remainders are retained. -/
theorem correction_limit_error_energy_exact (n : ℕ) :
    ‖hilbertDifference (correctionSynthesis n) + hilbertDifference limitResidual‖ ^ 2 =
      ‖rawMobiusDerivativeResidual (n + 1)‖ ^ 2 -
      2 * inner ℝ (rawMobiusDerivativeResidual (n + 1))
        (hilbertDifference (limitProjection - projection n)) +
      ‖hilbertDifference (limitProjection - projection n)‖ ^ 2 := by
  rw [correction_limit_error_exact, norm_sub_sq_real]

/-- Dimension-independent bound for every Hilbert test, including moving tests. -/
theorem correction_limit_test_bound (n : ℕ) (f : ThresholdHilbert) :
    |inner ℝ f (hilbertDifference (correctionSynthesis n)) +
      inner ℝ f (hilbertDifference limitResidual)| ≤
      ‖f‖ * (‖rawMobiusDerivativeResidual (n + 1)‖ +
        2 * ‖limitProjection - projection n‖) := by
  rw [← inner_add_right, correction_limit_error_exact]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add_right
        (hilbertDifference_norm_le _) _)) (norm_nonneg _))

theorem correction_limit_test_sq_bound (n : ℕ) (f : ThresholdHilbert) :
    |inner ℝ f (hilbertDifference (correctionSynthesis n)) +
      inner ℝ f (hilbertDifference limitResidual)| ^ 2 ≤
      2 * ‖f‖ ^ 2 * (‖rawMobiusDerivativeResidual (n + 1)‖ ^ 2 +
        4 * (energy n - limitEnergy)) := by
  have hb := correction_limit_test_bound n f
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
  have he := energy_eq_limit_add n
  have ht : (‖rawMobiusDerivativeResidual (n + 1)‖ +
      2 * ‖limitProjection - projection n‖) ^ 2 ≤
      2 * (‖rawMobiusDerivativeResidual (n + 1)‖ ^ 2 +
        4 * (energy n - limitEnergy)) := by
    nlinarith [sq_nonneg (‖rawMobiusDerivativeResidual (n + 1)‖ -
      2 * ‖limitProjection - projection n‖)]
  calc
    _ ≤ (‖f‖ * (‖rawMobiusDerivativeResidual (n + 1)‖ +
        2 * ‖limitProjection - projection n‖)) ^ 2 := hs
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left ht (sq_nonneg ‖f‖)
      nlinarith

theorem correction_limit_budget_tendsto_zero :
    Tendsto (fun n => ‖rawMobiusDerivativeResidual (n + 1)‖ +
      2 * ‖limitProjection - projection n‖) atTop (𝓝 0) := by
  have hg := ((tendsto_const_nhds (x := limitProjection)).sub projection_tendsto).norm
  have hr := rawMobiusDerivativeResidual_norm_tendsto_zero.comp
    (tendsto_add_atTop_nat 1)
  simpa using hr.add (hg.const_mul 2)

/-- The same estimate for the actual arithmetic rows; its limit is not deleted. -/
theorem signedCorrectionRow_limit_sq_bound (n i : ℕ) :
    |signedCorrectionRow n i + inner ℝ limitResidual (derivativeAdjointRow i)| ^ 2 ≤
      2 * ‖derivativeAtom i‖ ^ 2 *
        (‖rawMobiusDerivativeResidual (n + 1)‖ ^ 2 +
          4 * (energy n - limitEnergy)) := by
  simpa only [signedCorrectionRow_eq_pairing, fixedMismatch_limit_eq_adjoint_pairing]
    using correction_limit_test_sq_bound n (derivativeAtom i)

/-- Zero extension permits Abel summation without changing any finite coefficient. -/
def correctionCoefficient (n j : ℕ) : ℝ :=
  if h : j < n then correctionVector n ⟨j, h⟩ else 0

def derivativeRowKernel (i j : ℕ) : ℝ :=
  inner ℝ (derivativeAtom i) (derivativeAtom j)

/-- Exact boundary minus the entire signed first-difference sum. -/
theorem signedCorrectionRow_eq_abel (n i : ℕ) :
    signedCorrectionRow n i =
      primitive (correctionCoefficient n) n * derivativeRowKernel i n -
        ∑ k ∈ Finset.range n, primitive (correctionCoefficient n) (k + 1) *
          difference (derivativeRowKernel i) k := by
  have he : signedCorrectionRow n i =
      ∑ j ∈ Finset.range n, correctionCoefficient n j * derivativeRowKernel i j := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [correctionCoefficient, derivativeRowKernel]
  rw [he, sum_eq_value]
  rfl

/-- Second Abel form, preserving both boundary terms and the signed interior. -/
theorem signedCorrectionRow_eq_secondAbel (n i : ℕ) :
    signedCorrectionRow n i =
      secondValue (correctionCoefficient n) (derivativeRowKernel i) n := by
  rw [signedCorrectionRow_eq_abel]
  exact value_eq_secondValue _ _ _

/-- Cofinal smallness is sufficient because every row already has a limit. -/
theorem signedCorrectionRow_cofinal_iff_residual_zero :
    (∀ i : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, |signedCorrectionRow n i| < ε) ↔ limitResidual = 0 := by
  constructor
  · intro h
    apply fixedMismatch_limits_iff_residual_zero.mp
    intro i
    have hz : -inner ℝ limitResidual (derivativeAdjointRow i) = 0 := by
      by_contra hne
      let L := -inner ℝ limitResidual (derivativeAdjointRow i)
      have hp : 0 < |L| / 2 := by
        have := abs_pos.mpr hne
        change 0 < |-inner ℝ limitResidual (derivativeAdjointRow i)| / 2
        positivity
      have hl : ∀ᶠ n : ℕ in atTop, |L| / 2 < |signedCorrectionRow n i| :=
        (signedCorrectionRow_tendsto i).abs.eventually_const_lt (by
          change |L| / 2 < |L|
          have := abs_pos.mpr hne
          dsimp [L]
          linarith)
      obtain ⟨n, hn, hn'⟩ := ((h i (|L| / 2) hp).and_eventually hl).exists
      linarith
    have hc := signedCorrectionRow_tendsto i
    rw [hz] at hc
    simpa only [fixedMismatch_eq_raw_sub_signedCorrectionRow, sub_zero] using
      (raw_stage_derivative_pairing_tendsto_zero i).sub hc
  · intro hz i ε hε
    have hc := signedCorrectionRow_tendsto i
    simp only [hz, inner_zero_left, neg_zero] at hc
    exact (hc.abs.eventually_lt_const (by simpa using hε)).frequently

/-- CONDITIONAL RESEARCH REDUCTION. No cancellation provider is assumed proved. -/
theorem riemannHypothesis_of_cofinal_signedCorrectionRow
    (h : ∀ i : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, |signedCorrectionRow n i| < ε) : RiemannHypothesis :=
  riemannHypothesis_of_fixedMismatch_limits
    (fixedMismatch_limits_iff_residual_zero.mpr
      (signedCorrectionRow_cofinal_iff_residual_zero.mp h))

/-- The surviving conductor-two correction has the opposite sign to mismatch. -/
theorem signedCorrectionRow_first_tendsto :
    Tendsto (fun n => signedCorrectionRow n 0) atTop
      (𝓝 (limitEnergy + inner ℝ limitResidual firstRowRemainder)) := by
  have he := fixedMismatch_first_limit_exact
  rw [fixedMismatch_limit_eq_adjoint_pairing] at he
  simpa only [he, neg_sub, sub_neg_eq_add, add_comm] using signedCorrectionRow_tendsto 0

/-- Uniform testing of the error about its identified limit. No limit for f_n is needed. -/
theorem correction_limit_moving_test_tendsto_zero (f : ℕ → ThresholdHilbert)
    (C : ℝ) (hf : ∀ n, ‖f n‖ ≤ C) :
    Tendsto (fun n => inner ℝ (f n) (hilbertDifference (correctionSynthesis n)) +
      inner ℝ (f n) (hilbertDifference limitResidual)) atTop (𝓝 0) := by
  apply squeeze_zero_norm
    (fun n => (correction_limit_test_bound n (f n)).trans
      (mul_le_mul_of_nonneg_right (hf n) (by positivity)))
  simpa using correction_limit_budget_tendsto_zero.const_mul C

/-- The concrete signed Abel estimate is equivalent to vanishing of the residual.
The absolute value is taken only after the boundary and interior are combined. -/
theorem correctionAbel_cofinal_iff_residual_zero :
    (∀ i : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |primitive (correctionCoefficient n) n * derivativeRowKernel i n -
        ∑ k ∈ Finset.range n, primitive (correctionCoefficient n) (k + 1) *
          difference (derivativeRowKernel i) k| < ε) ↔ limitResidual = 0 := by
  simpa only [signedCorrectionRow_eq_abel] using
    signedCorrectionRow_cofinal_iff_residual_zero

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
