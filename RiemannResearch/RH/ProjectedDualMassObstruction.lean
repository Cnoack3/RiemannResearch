import RiemannResearch.Analysis.CriticalCutoffGrowth
import RiemannResearch.Analysis.StretchedCutoffRescaling
import RiemannResearch.RH.ParetoCriticalMellinCutoff
import RiemannResearch.RH.ProjectedDualMellinWitness
import RiemannResearch.RH.ProjectedDualColumnConcentration

/-!
# A critical-zero obstruction to strict-margin inverse-column mass bounds

Source: completion of the user's requested Lean obstruction, 28 September 2026.
The analytic split and finite-dual argument are independently derived in the
companion modules; see ProjectedDualMassObstructionAudit20260928.md.

The arithmetic energy exponent is supplied by a checked unconditional theorem.
A critical-line zeta zero is an explicit premise in every obstruction theorem.
Existence of such a zero remains an Open formalization dependency here; it is
not added as an axiom. RH is neither assumed nor proved.

The selected d is fixed in {2,3}, before quantifying over b<a. The resulting
divergence refutes even separate cofinal bounds and separate strict exponents
for each column. The endpoint b=a and signed physical-tail criteria are
not refuted by these theorems.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis

/-- The finite projection estimate assembled with the explicit arithmetic
energy premise, at its unchanged exponent. -/
theorem projectedDualError_two_three_eventual_stretched_fourth
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ N : ℕ in atTop, ‖tailError N‖ ^ 2 ≤
      8 + C * (N : ℝ) * Real.exp (-a *
        logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, d = 2 ∨ d = 3 →
      ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 4 ≤
        D * projectedDualCoefficientMass n d ^ 2 *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) := by
  obtain ⟨D, hD, hnorm⟩ := eighth_normalized_stretched_energy ha hC
    (fun N => ‖tailError N‖ ^ 2) henergy
  refine ⟨530 * D, by positivity, ?_⟩
  filter_upwards [hnorm, eventually_ge_atTop (24 : ℕ)] with n hen hn
  intro d hd
  have hN : 3 ≤ n / 8 := by omega
  have hcut : 4 * (n / 8 + 1) ≤ n + 1 := by omega
  have hq :
      ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 4 ≤
        530 * (projectedDualCoefficientMass n d ^ 2 * ‖tailError (n / 8)‖ ^ 2 /
          (((n / 8 : ℕ) : ℝ) + 1)) := by
    rcases hd with rfl | rfl
    · have hh := projectedDualError_two_fourth_le_mass n (n / 8)
        (by omega) (by omega)
      calc
        _ ≤ 270 * (projectedDualCoefficientMass n 2 ^ 2 * ‖tailError (n / 8)‖ ^ 2 /
            (((n / 8 : ℕ) : ℝ) + 1)) := by convert hh using 1 <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    · convert projectedDualError_three_fourth_le_mass n (n / 8) hN hcut using 1 <;> ring
  calc
    _ ≤ 530 * (projectedDualCoefficientMass n d ^ 2 * ‖tailError (n / 8)‖ ^ 2 /
        (((n / 8 : ℕ) : ℝ) + 1)) := hq
    _ = (530 * projectedDualCoefficientMass n d ^ 2) *
        (‖tailError (n / 8)‖ ^ 2 / (((n / 8 : ℕ) : ℝ) + 1)) := by ring
    _ ≤ (530 * projectedDualCoefficientMass n d ^ 2) *
        (D * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hen (by positivity)
    _ = _ := by ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open Filter RiemannResearch.Analysis
open scoped Topology BigOperators

/-- At any critical-line zero, one fixed small inverse column violates every
strictly smaller stretched exponent. The arithmetic energy premise is explicit. -/
theorem coefficient_mass_stretched_barrier_of_critical_zero
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (s : ℂ) (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) :
    ∃ d : ℕ, (d = 2 ∨ d = 3) ∧ ∀ b : ℝ, b < a →
      Tendsto (fun n : ℕ => Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (n : ℝ))) * projectedDualCoefficientMass n d ^ 2) atTop atTop := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro he
    rw [he] at hs
    norm_num at hs
  obtain ⟨d, hd, hM⟩ : ∃ d : ℕ, (d = 2 ∨ d = 3) ∧
      paretoMellin (coefficientRiesz d) s ≠ 0 := by
    rcases coefficientRiesz_two_or_three_mellin_ne_zero s hs0 with h2 | h3
    · exact ⟨2, Or.inl rfl, h2⟩
    · exact ⟨3, Or.inr rfl, h3⟩
  obtain ⟨D, hD, herr⟩ :=
    projectedDualError_two_three_eventual_stretched_fourth ha hC henergy
  have hφ : Tendsto (fun n : ℕ =>
      logProductPower (1 / 11) (6 + Real.log (n : ℝ))) atTop atTop :=
    (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop 6
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  refine ⟨d, hd, ?_⟩
  intro b hb
  apply mass_barrier_of_critical_cutoff
    (fun n => logProductPower (1 / 11) (6 + Real.log (n : ℝ)))
    (fun n => projectedDualCoefficientMass n d)
    (fun n => ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖)
    hφ (fun n => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (fun _ => norm_nonneg _) a D 12 ‖paretoMellin (coefficientRiesz d) s‖
    hD (by norm_num) (norm_pos_iff.mpr hM) _ _ b hb
  · filter_upwards [herr] with n hn
    exact hn d hd
  · intro n R hR
    have h := paretoMellin_critical_cutoff
      (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))
      (projectedDualError_sequence_abs_le n d hd) s hs R hR
    rw [projectedDualError_mellin_at_zero n d hd s hs0 hs1 hz] at h
    exact h

/-- The repository's unconditional arithmetic theorem supplies the exponent.
Existence of a critical-line zero remains an explicit premise; RH is not used. -/
theorem exists_coefficient_mass_stretched_barrier_of_critical_zero
    (s : ℂ) (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) :
    ∃ a : ℝ, 0 < a ∧ ∃ d : ℕ, (d = 2 ∨ d = 3) ∧ ∀ b : ℝ, b < a →
      Tendsto (fun n : ℕ => Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (n : ℝ))) * projectedDualCoefficientMass n d ^ 2) atTop atTop := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  exact ⟨a, ha, coefficient_mass_stretched_barrier_of_critical_zero ha hC he s hs hz⟩

/-- This refutes even a separate strict exponent and separate cofinal set for
each fixed column, under the displayed critical-zero premise. -/
theorem not_cofinal_stretched_coefficient_mass_of_critical_zero
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (s : ℂ) (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) :
    ¬ (∀ d : ℕ, 1 < d → ∃ b : ℝ, b < a ∧ ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        projectedDualCoefficientMass n d ^ 2 ≤ K) := by
  intro hmass
  obtain ⟨d, hd, hdiv⟩ :=
    coefficient_mass_stretched_barrier_of_critical_zero ha hC henergy s hs hz
  obtain ⟨b, hb, K, hK⟩ := hmass d (by rcases hd with rfl | rfl <;> omega)
  obtain ⟨n, hle, hgt⟩ := (hK.and_eventually ((hdiv b hb).eventually_gt_atTop K)).exists
  exact (not_lt_of_ge hle) hgt

/-- The effective-support/l2 budget implies the refuted mass budget. Its leakage
and support estimates are all retained at the same cofinal indices. -/
theorem not_cofinal_stretched_l2_concentration_of_critical_zero
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (s : ℂ) (hs : s.re = 1 / 2) (hz : riemannZeta s = 0) :
    ¬ (∀ d : ℕ, 1 < d → ∃ b : ℝ, b < a ∧ ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      ∃ (I : Finset (Fin n)) (ρ : ℝ), 0 ≤ ρ ∧
        (∑ i ∈ Iᶜ, projectedDualColumn n d i ^ 2) ≤
          ρ * projectedDualColumnEnergy n d ∧
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          (((I.card : ℝ) + (Iᶜ.card : ℝ) * ρ) * projectedDualColumnEnergy n d) ≤ K) := by
  intro hbound
  apply not_cofinal_stretched_coefficient_mass_of_critical_zero ha hC henergy s hs hz
  intro d hd
  obtain ⟨b, hb, K, hK⟩ := hbound d hd
  refine ⟨b, hb, 2 * K, hK.mono ?_⟩
  rintro n ⟨I, ρ, hρ, hleak, hbudget⟩
  have hmass := (projectedDualCoefficientMass_sq_le_split_energy n d I).trans
    (mul_le_mul_of_nonneg_left
      (projectedDualSplitEnergy_le_effective_support n d I ρ hleak) (by norm_num : (0:ℝ) ≤ 2))
  have he := mul_le_mul_of_nonneg_left hmass
    (Real.exp_pos (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))).le
  nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
