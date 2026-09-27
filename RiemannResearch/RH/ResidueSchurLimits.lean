import RiemannResearch.RH.ResidueProjectionSchur
import RiemannResearch.RH.ResidualGainObstruction
import RiemannResearch.RH.FiniteDilationFamilyGap

/-!
# Infinite Schur gains and the remaining saturation condition

Source: the user's ResidueProjectionSchur.md, 22 September 2026, for the
finite-stage formulas. This continuation derives their exact infinite sums
using the existing projection limit and Mathlib summation results.
The relative-gain criterion uses Analysis.ResidualGainProduct.

Stage n uses conductors 2,...,n+1; innovation n adjoins conductor n+2.
All norms and Gram entries are the complete infinite Pareto quantities.

Established: exact Schur tail sums, finite-stage error positivity, an exact
survival product, and the equivalence of zero limiting error with
nonsummability of the actual relative gains.
Conditional research reductions: the RH implications in this module.
Open: Schur saturation, equivalently nonsummability of the relative gains.
No such arithmetic estimate is assumed to have been proved.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur

theorem schur_gain_eq_mode_sq (n : ℕ) :
    (schurEta n)^2 / schurSigma n = (modeAlpha n)^2 := by
  have h₁ := captured_schur_step n
  have h₂ := captured_succ_mode n
  linarith

theorem schur_gain_sum_eq_captured (n : ℕ) :
    (∑ j ∈ Finset.range n, (schurEta j)^2 / schurSigma j) = captured n := by
  simp only [schur_gain_eq_mode_sq]
  rw [mode_sum_eq_one_sub_energy]
  have h := error_eq_one_sub_captured n
  change energy n = 1 - captured n at h
  linarith

theorem schur_gain_hasSum :
    HasSum (fun j => (schurEta j)^2 / schurSigma j) (1 - limitEnergy) := by
  simpa only [schur_gain_eq_mode_sq] using modeAlpha_sq_hasSum

theorem schur_gain_tsum :
    (∑' j, (schurEta j)^2 / schurSigma j) = 1 - limitEnergy :=
  schur_gain_hasSum.tsum_eq

/-- The tail measures distance to the limiting projection, not to the target. -/
theorem schur_gain_tail_hasSum (n : ℕ) :
    HasSum (fun j => (schurEta (j+n))^2 / schurSigma (j+n))
      (energy n - limitEnergy) := by
  have h := (hasSum_nat_add_iff'
    (f := fun j => (schurEta j)^2 / schurSigma j)
    (g := 1 - limitEnergy) n).mpr schur_gain_hasSum
  rw [schur_gain_sum_eq_captured] at h
  have he : (1 - limitEnergy) - captured n = energy n - limitEnergy := by
    have hE := error_eq_one_sub_captured n
    change energy n = 1 - captured n at hE
    linarith
  simpa only [he] using h

theorem schur_gain_tail_tsum (n : ℕ) :
    (∑' j, (schurEta (j+n))^2 / schurSigma (j+n)) =
      energy n - limitEnergy := (schur_gain_tail_hasSum n).tsum_eq

theorem energy_eq_limit_add_schur_tail (n : ℕ) :
    energy n = limitEnergy +
      ∑' j, (schurEta (j+n))^2 / schurSigma (j+n) := by
  rw [schur_gain_tail_tsum]
  ring

theorem schur_gain_tail_eq_projection_distance (n : ℕ) :
    (∑' j, (schurEta (j+n))^2 / schurSigma (j+n)) =
      ‖limitProjection - projection n‖ ^ 2 := by
  rw [schur_gain_tail_tsum]
  have h := energy_eq_limit_add n
  linarith

theorem coefficient_error_bound_schur_tail (n m : ℕ) :
    ‖limitCoefficient m - coefficient n m‖ ^ 2 ≤
      ‖mobiusDifferenceCLM m‖ ^ 2 *
        (∑' j, (schurEta (j+n))^2 / schurSigma (j+n)) := by
  rw [schur_gain_tail_tsum]
  exact coefficient_error_bound n m

theorem schur_gain_after_two_hasSum :
    HasSum (fun j => (schurEta (j+1))^2 / schurSigma (j+1))
      (1 - Real.log 2 - limitEnergy) := by
  simpa only [energy_one] using schur_gain_tail_hasSum 1

theorem captured_tendsto :
    Tendsto captured atTop (𝓝 (1 - limitEnergy)) := by
  have he (n : ℕ) : captured n = 1 - energy n := by
    have h := error_eq_one_sub_captured n
    change energy n = 1 - captured n at h
    linarith
  change Tendsto (fun n => captured n) atTop (𝓝 (1 - limitEnergy))
  simpa only [he] using
    (tendsto_const_nhds.sub energy_tendsto :
      Tendsto (fun n => 1 - energy n) atTop (𝓝 (1 - limitEnergy)))

/-- Q tends to one exactly when the actual limiting projection defect vanishes. -/
theorem captured_tendsto_one_iff_limitEnergy_zero :
    Tendsto captured atTop (𝓝 1) ↔ limitEnergy = 0 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique captured_tendsto h
    linarith
  · intro hD
    simpa only [hD, sub_zero] using captured_tendsto

theorem captured_tendsto_one_iff_norm :
    Tendsto captured atTop (𝓝 1) ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
  captured_tendsto_one_iff_limitEnergy_zero.trans
    (limitEnergy_zero_iff_mem.trans projection_norm_tendsto_zero_iff_mem.symm)

/-- Existence of coefficient limits is unconditional; their Mobius values
are equivalent to saturation of the complete inverse-Gram captured energy. -/
theorem captured_tendsto_one_iff_coefficients_tendsto_mobius :
    Tendsto captured atTop (𝓝 1) ↔
      ∀ d : ℕ, 1 < d →
        Tendsto (fun n => coefficient n d) atTop
          (𝓝 (-(ArithmeticFunction.moebius d : ℝ))) := by
  exact (captured_tendsto_one_iff_limitEnergy_zero.trans
    limitEnergy_zero_iff_mem).trans
    (coefficients_tendsto_mobius_iff.trans limitCoefficients_eq_mobius_iff_mem).symm

theorem captured_tendsto_one_iff_correction_tendsto_zero :
    Tendsto captured atTop (𝓝 1) ↔
      ∀ d : ℕ, 1 < d →
        Tendsto (fun n => GramMobiusCorrection.correction n d) atTop (𝓝 0) :=
  captured_tendsto_one_iff_norm.trans GramMobiusCorrection.correction_limits_iff_norm.symm

/-- Conditional research reduction. Q -> 1 remains an explicit open hypothesis. -/
theorem riemannHypothesis_of_captured_tendsto_one
    (h : Tendsto captured atTop (𝓝 1)) : RiemannHypothesis :=
  riemannHypothesis_of_projection_norm_tendsto_zero
    (captured_tendsto_one_iff_norm.mp h)

theorem schur_saturation_iff_norm :
    (∑' j, (schurEta j)^2 / schurSigma j) = 1 ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) := by
  simp only [schur_gain_eq_mode_sq]
  exact mode_parseval_iff_one_mem.trans projection_norm_tendsto_zero_iff_mem.symm

/-- A common multiple gives an explicit positive error at each finite stage. -/
theorem projection_factorial_zero (n : ℕ) :
    hilbertSequence (projection n) (Nat.factorial (n+1)) = 0 := by
  rw [GramMobiusCorrection.projection_eq_inverseGram_synthesis]
  change hilbertSequenceLinear (∑ i : Fin n,
    GramMobiusCorrection.canonicalVector n i • residueAtom i.val) _ = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  change GramMobiusCorrection.canonicalVector n i *
    hilbertSequence (residueAtom i.val) (Nat.factorial (n+1)) = 0
  rw [residueAtom, normalizedResidueHilbert_sequence]
  simp [ArithmeticCumulative.residueFraction, Nat.mod_eq_zero_of_dvd
    (Nat.dvd_factorial (by omega : 0 < i.val+2) (by omega : i.val+2 ≤ n+1))]

theorem finite_energy_factorial_floor (n : ℕ) :
    positiveWeight (Nat.factorial (n+1)) ≤ energy n :=
  hilbert_error_lower_of_zero_coordinate (projection n)
    (Nat.factorial (n+1)) (Nat.factorial_pos _) (projection_factorial_zero n)

theorem finite_energy_pos (n : ℕ) : 0 < energy n := by
  have hp : 0 < positiveWeight (Nat.factorial (n+1)) := by
    unfold positiveWeight
    positivity
  exact hp.trans_le (finite_energy_factorial_floor n)

theorem energy_schur_step (n : ℕ) :
    energy (n+1) = energy n - (schurEta n)^2 / schurSigma n := by
  have h₀ := error_eq_one_sub_captured n
  have h₁ := error_eq_one_sub_captured (n+1)
  change energy n = _ at h₀
  change energy (n+1) = _ at h₁
  rw [captured_schur_step] at h₁
  linarith

/-- The normalized gain is the actual Schur decrement divided by current error. -/
theorem projectionRelativeGain_eq_schur (n : ℕ) :
    projectionRelativeGain n =
      (schurEta n)^2 / (schurSigma n * energy n) := by
  unfold projectionRelativeGain
  rw [energy_schur_step]
  ring

theorem relativeGain_lt_one (n : ℕ) : projectionRelativeGain n < 1 := by
  apply (div_lt_one (finite_energy_pos n)).mpr
  linarith [finite_energy_pos (n+1)]

theorem energy_relativeGain_step (n : ℕ) :
    energy (n+1) = energy n * (1 - projectionRelativeGain n) := by
  unfold projectionRelativeGain
  field_simp [ne_of_gt (finite_energy_pos n)]
  ring

theorem energy_relativeGain_product (n : ℕ) :
    energy n = energy 0 *
      ∏ j ∈ Finset.range n, (1 - projectionRelativeGain j) :=
  Analysis.ResidualGain.recurrence_eq_mul_product energy_relativeGain_step n

/-- No RH assumption is required for the exact infinite-product criterion. -/
theorem energy_zero_iff_relativeGain_not_summable :
    Tendsto energy atTop (𝓝 0) ↔ ¬Summable projectionRelativeGain :=
  Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
    (finite_energy_pos 0) projectionRelativeGain_nonneg relativeGain_lt_one
    energy_relativeGain_step

theorem schur_saturation_iff_relativeGain_not_summable :
    (∑' j, (schurEta j)^2 / schurSigma j) = 1 ↔
      ¬Summable projectionRelativeGain := by
  rw [← energy_zero_iff_relativeGain_not_summable]
  have he : Tendsto energy atTop (𝓝 0) ↔ limitEnergy = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique energy_tendsto h
    · intro h
      simpa only [h] using energy_tendsto
  rw [he, schur_gain_tsum]
  constructor <;> intro h <;> linarith

/-- Fixed coefficients have finite total variation, without target identification. -/
theorem coefficient_total_variation_summable (m : ℕ) :
    Summable (fun n => ‖coefficient (n+1) m - coefficient n m‖) := by
  have he (n : ℕ) : coefficient (n+1) m - coefficient n m =
      modeAlpha n * modeCoefficient m n := by
    unfold coefficient
    rw [projection_succ_mode, map_add, map_smul]
    change coefficient n m + modeAlpha n * modeCoefficient m n - coefficient n m = _
    ring
  simpa only [he] using mode_coefficient_series_norm_summable m

/-- Conditional research reduction. Schur saturation remains open. -/
theorem riemannHypothesis_of_schur_saturation
    (h : (∑' j, (schurEta j)^2 / schurSigma j) = 1) : RiemannHypothesis := by
  apply riemannHypothesis_of_mode_parseval
  simpa only [schur_gain_eq_mode_sq] using h

/-- Conditional research reduction. Actual relative-gain divergence remains open. -/
theorem riemannHypothesis_of_relativeGain_not_summable
    (h : ¬Summable projectionRelativeGain) : RiemannHypothesis :=
  riemannHypothesis_of_schur_saturation
    (schur_saturation_iff_relativeGain_not_summable.mpr h)

open TailCapacity IntegerDPP GramMobiusCorrection

/-- At stage n+1, the Schur gains following conductor 2 exactly exhaust the increment. -/
theorem captured_eq_log_two_add_schur_sum (n : ℕ) :
    captured (n + 1) = Real.log 2 +
      ∑ j ∈ Finset.range n, (schurEta (j + 1)) ^ 2 / schurSigma (j + 1) := by
  induction n with
  | zero => simpa using captured_one
  | succ n ih =>
    rw [captured_schur_step, ih, Finset.sum_range_succ]
    ring

/-- This is an exact defect identity, with no assertion that the defect is zero. -/
theorem limitEnergy_eq_one_sub_log_sub_schur_tsum :
    limitEnergy = 1 - Real.log 2 -
      ∑' j, (schurEta (j + 1)) ^ 2 / schurSigma (j + 1) := by
  have h := schur_gain_after_two_hasSum.tsum_eq
  linarith

/-- Saturation is equivalent to a vanishing limiting defect, not a consequence of summability. -/
theorem schur_tail_saturation_iff_energy_zero :
    (∑' j, (schurEta (j + 1)) ^ 2 / schurSigma (j + 1)) =
        1 - Real.log 2 ↔ limitEnergy = 0 := by
  rw [schur_gain_after_two_hasSum.tsum_eq]
  constructor <;> intro h <;> linarith

/-- Exact criterion for the user's full, unsquared Pareto norm convergence. -/
theorem schur_tail_saturation_iff_norm_tendsto_zero :
    (∑' j, (schurEta (j + 1)) ^ 2 / schurSigma (j + 1)) =
        1 - Real.log 2 ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
  schur_tail_saturation_iff_energy_zero.trans
    (limitEnergy_zero_iff_mem.trans projection_norm_tendsto_zero_iff_mem.symm)

/-- Conditional RH reduction. The Schur saturation equality remains the open input. -/
theorem riemannHypothesis_of_schur_tail_saturation
    (h : (∑' j, (schurEta (j + 1)) ^ 2 / schurSigma (j + 1)) =
      1 - Real.log 2) : RiemannHypothesis :=
  riemannHypothesis_of_projection_norm_tendsto_zero
    (schur_tail_saturation_iff_norm_tendsto_zero.mp h)

/-- The unsquared full error always converges, to the square root of the actual defect. -/
theorem projection_norm_tendsto_sqrt_limitEnergy :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop
      (𝓝 (Real.sqrt limitEnergy)) := by
  have hs : Real.sqrt limitEnergy = ‖limitResidual‖ := by
    change Real.sqrt (‖limitResidual‖ ^ 2) = ‖limitResidual‖
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hs]
  exact projection_norm_error_tendsto

/-- Equation (33): six equivalent descriptions of saturation for the actual canonical
projections. Each displayed condition separately suffices; none is asserted to hold. -/
theorem canonical_saturation_equivalences :
    (limitEnergy = 0 ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0)) ∧
    (limitEnergy = 0 ↔ Tendsto captured atTop (𝓝 1)) ∧
    (limitEnergy = 0 ↔
      (∑' j, (schurEta (j + 1)) ^ 2 / schurSigma (j + 1)) =
        1 - Real.log 2) ∧
    (limitEnergy = 0 ↔
      ∀ d : ℕ, 1 < d → Tendsto (fun n => coefficient n d) atTop
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ∧
    (limitEnergy = 0 ↔
      ∀ d : ℕ, 1 < d → Tendsto (fun n => correction n d) atTop (𝓝 0)) := by
  have hn : limitEnergy = 0 ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
    limitEnergy_zero_iff_mem.trans projection_norm_tendsto_zero_iff_mem.symm
  have hc :
      (∀ d : ℕ, 1 < d → Tendsto (fun n => coefficient n d) atTop
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ↔
        Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
    coefficients_tendsto_mobius_iff.trans
      (limitCoefficients_eq_mobius_iff_mem.trans
        projection_norm_tendsto_zero_iff_mem.symm)
  exact ⟨hn, hn.trans captured_tendsto_one_iff_norm.symm,
    schur_tail_saturation_iff_energy_zero.symm, hn.trans hc.symm,
    hn.trans correction_limits_iff_norm.symm⟩

/-- The final classical equivalence, retaining its external Báez--Duarte direction
as an explicit premise. No provider of that premise or of saturation is introduced. -/
theorem projection_norm_iff_riemannHypothesis_of_baez_duarte
    (hBaezDuarte : RiemannHypothesis → hilbertOne ∈ closedSpace) :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_projection_norm_tendsto_zero
  · intro hRH
    exact projection_norm_tendsto_zero_iff_mem.mpr (hBaezDuarte hRH)

end RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur
