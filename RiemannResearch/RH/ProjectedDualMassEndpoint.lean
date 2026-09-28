import RiemannResearch.Analysis.CriticalCutoffEndpoint
import RiemannResearch.RH.ProjectedDualMassObstructionUnconditional
import RiemannResearch.RH.SmallDualCriticalZeros

/-!
# Both-column endpoint mass obstruction

Source: elementary critical-cutoff optimization, combined with the repository's
proved Mellin witnesses and canonical-energy estimate. The Zeta23 import supplies
arbitrarily high actual critical zeros; SmallDualCriticalZeros detects both columns.
The endpoint lower bound retains the quadratic profile loss. It does not refute
bounded endpoint mass without that loss and does not settle signed pairing or RH.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis

/-- Every finite projected dual has a logarithmic error-versus-mass lower
bound. No Mertens or canonical-energy estimate is needed for this statement. -/
theorem projectedDualError_log_mass_lower_bound_of_mellin_witness
    (d : ℕ) (hd : d = 2 ∨ d = 3)
    (s : ℂ) (hs : s.re = 1 / 2) (hz : riemannZeta s = 0)
    (hM : paretoMellin (coefficientRiesz d) s ≠ 0) (n : ℕ) :
    ‖paretoMellin (coefficientRiesz d) s‖ ^ 2 / 8 ≤
      ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 2 *
        Real.log (4 * (12 + projectedDualCoefficientMass n d +
          ‖paretoMellin (coefficientRiesz d) s‖) /
            ‖paretoMellin (coefficientRiesz d) s‖) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro he
    rw [he] at hs
    norm_num at hs
  apply critical_cutoff_logarithmic_tradeoff
    (projectedDualCoefficientMass n d)
    ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖
    12 ‖paretoMellin (coefficientRiesz d) s‖
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (norm_nonneg _) (by norm_num) (norm_pos_iff.mpr hM)
  intro R hR
  have h := paretoMellin_critical_cutoff
    (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))
    (projectedDualError_sequence_abs_le n d hd) s hs R hR
  rw [projectedDualError_mellin_at_zero n d hd s hs0 hs1 hz] at h
  exact h

/-- An eventual lower bound at the arithmetic exponent, retaining the quadratic
cutoff-profile loss. The critical zero is explicit in this analytic interface. -/
theorem coefficient_mass_endpoint_lower_bound_of_mellin_witness
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (d : ℕ) (hd : d = 2 ∨ d = 3)
    (s : ℂ) (hs : s.re = 1 / 2) (hz : riemannZeta s = 0)
    (hM : paretoMellin (coefficientRiesz d) s ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      κ ≤ logProductPower (1 / 11) (6 + Real.log (n : ℝ)) ^ 2 *
        (Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          projectedDualCoefficientMass n d ^ 2) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro he
    rw [he] at hs
    norm_num at hs
  obtain ⟨D, hD, herr⟩ :=
    projectedDualError_two_three_eventual_stretched_fourth ha hC henergy
  have hφ : Tendsto (fun n : ℕ =>
      logProductPower (1 / 11) (6 + Real.log (n : ℝ))) atTop atTop :=
    (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop 6
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  apply mass_endpoint_lower_bound_of_critical_cutoff
    (fun n => logProductPower (1 / 11) (6 + Real.log (n : ℝ)))
    (fun n => projectedDualCoefficientMass n d)
    (fun n => ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖)
    hφ (fun n => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (fun _ => norm_nonneg _) a D 12 ‖paretoMellin (coefficientRiesz d) s‖
    ha hD (by norm_num) (norm_pos_iff.mpr hM)
  · filter_upwards [herr] with n hn
    exact hn d hd
  · intro n R hR
    have h := paretoMellin_critical_cutoff
      (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))
      (projectedDualError_sequence_abs_le n d hd) s hs R hR
    rw [projectedDualError_mellin_at_zero n d hd s hs0 hs1 hz] at h
    exact h

/-- A single positive endpoint lower bound holds for both columns, at the
unchanged exponent of the given arithmetic estimate. -/
theorem coefficient_mass_endpoint_lower_bound_both
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, d = 2 ∨ d = 3 →
      κ ≤ logProductPower (1 / 11) (6 + Real.log (n : ℝ)) ^ 2 *
        (Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          projectedDualCoefficientMass n d ^ 2) := by
  obtain ⟨s, hz, hs, _, _, h2, h3⟩ :=
    exists_common_small_dual_critical_mellin_witness_above 0
  obtain ⟨κ2, hk2, he2⟩ := coefficient_mass_endpoint_lower_bound_of_mellin_witness
    ha hC henergy 2 (Or.inl rfl) s hs hz h2
  obtain ⟨κ3, hk3, he3⟩ := coefficient_mass_endpoint_lower_bound_of_mellin_witness
    ha hC henergy 3 (Or.inr rfl) s hs hz h3
  refine ⟨min κ2 κ3, lt_min hk2 hk3, ?_⟩
  filter_upwards [he2, he3] with n hn2 hn3
  intro d hd
  rcases hd with rfl | rfl
  · exact (min_le_left _ _).trans hn2
  · exact (min_le_right _ _).trans hn3

/-- Both columns have an unconditional endpoint obstruction. There are no
arithmetic, zero-existence, or RH hypotheses in this declaration. -/
theorem exists_coefficient_mass_endpoint_lower_bound_both :
    ∃ a : ℝ, 0 < a ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, d = 2 ∨ d = 3 →
        κ ≤ logProductPower (1 / 11) (6 + Real.log (n : ℝ)) ^ 2 *
          (Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
            projectedDualCoefficientMass n d ^ 2) := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  exact ⟨a, ha, coefficient_mass_endpoint_lower_bound_both ha hC he⟩

/-- The strict-margin divergence holds for each of columns two and three,
with the same positive arithmetic exponent. -/
theorem exists_coefficient_mass_stretched_barrier_both :
    ∃ a : ℝ, 0 < a ∧ ∀ d : ℕ, d = 2 ∨ d = 3 → ∀ b : ℝ, b < a →
      Tendsto (fun n : ℕ =>
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          projectedDualCoefficientMass n d ^ 2) atTop atTop := by
  obtain ⟨a, ha, κ, hκ, hbound⟩ := exists_coefficient_mass_endpoint_lower_bound_both
  have hφ : Tendsto (fun n : ℕ =>
      logProductPower (1 / 11) (6 + Real.log (n : ℝ))) atTop atTop :=
    (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop 6
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  refine ⟨a, ha, ?_⟩
  intro d hd b hb
  apply mass_strict_growth_of_endpoint_lower_bound _
    (fun n => projectedDualCoefficientMass n d) hφ hκ _ b hb
  filter_upwards [hbound] with n hn
  exact hn d hd

/-- The endpoint normalized mass cannot tend to zero along any cofinal
subsequence, separately for either small column. -/
theorem exists_coefficient_mass_endpoint_subsequence_obstruction :
    ∃ a : ℝ, 0 < a ∧ ∀ d : ℕ, d = 2 ∨ d = 3 →
      ∀ seq : ℕ → ℕ, Tendsto seq atTop atTop →
        ¬ Tendsto (fun k =>
          logProductPower (1 / 11) (6 + Real.log (seq k : ℝ)) ^ 2 *
            (Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (seq k : ℝ))) *
              projectedDualCoefficientMass (seq k) d ^ 2)) atTop (𝓝 0) := by
  obtain ⟨a, ha, κ, hκ, hbound⟩ := exists_coefficient_mass_endpoint_lower_bound_both
  refine ⟨a, ha, ?_⟩
  intro d hd seq hseq hzero
  have hevent : ∀ᶠ k : ℕ in atTop,
      κ ≤ logProductPower (1 / 11) (6 + Real.log (seq k : ℝ)) ^ 2 *
        (Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (seq k : ℝ))) *
          projectedDualCoefficientMass (seq k) d ^ 2) := by
    filter_upwards [hseq.eventually hbound] with k hk
    exact hk d hd
  obtain ⟨k, hk, hlt⟩ := (hevent.and (hzero.eventually_lt_const hκ)).exists
  exact (not_lt_of_ge hk) hlt

/-- The error/mass tradeoff is unconditional for each small column and every
finite cutoff. It uses no Mertens or canonical-energy estimate. -/
theorem exists_projectedDualError_log_mass_lower_bound
    {d : ℕ} (hd : d = 2 ∨ d = 3) :
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ,
      L ^ 2 / 8 ≤
        ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 2 *
          Real.log (4 * (12 + projectedDualCoefficientMass n d + L) / L) := by
  obtain ⟨s, hz, hs, _, _, hM⟩ := exists_small_dual_critical_mellin_witness_above hd 0
  exact ⟨‖paretoMellin (coefficientRiesz d) s‖, norm_pos_iff.mpr hM,
    fun n => projectedDualError_log_mass_lower_bound_of_mellin_witness d hd s hs hz hM n⟩

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
