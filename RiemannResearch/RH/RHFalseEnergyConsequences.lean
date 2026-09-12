import RiemannResearch.RH.ParetoL1MellinBound
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Consequences of failure of RH and a subpolynomial-energy contradiction criterion

Source: user-provided argument,
RH_Canonical_Correlations_and_Spectral_Obstruction_20260912 (1).md,
Sections 6 and 13-14, and its analytic continuation of 12 September 2026.
The source motivates the consequences and the remaining energy problem.
The proof uses the already established actual Mellin identity, zeta reflection,
and the concrete weighted L1 estimates in ParetoL1MellinBound.

The consequences under a hypothetical zero or failure of RH are proved
implications, not assumptions of new arithmetic providers. The final
RH sufficient criterion is a CONDITIONAL RESEARCH REDUCTION: actual finite
legal witnesses, L1 convergence, and subpolynomial full signed energy remain
required inputs. This module does not construct those witnesses with that
energy control, assert the converse criterion, or prove RH unconditionally.
-/

namespace RiemannResearch.RH
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- Failure of Mathlib's actual RH yields a zero in the open right half-strip. -/
theorem exists_right_zero_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ (1/2 : ℝ) < s.re ∧ s.re < 1 := by
  by_contra hn
  apply h
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro s hz h0 h1
  have hright (z : ℂ) (hz : riemannZeta z = 0) (h1 : z.re < 1) :
      z.re ≤ 1/2 := by
    by_contra hb
    exact hn ⟨z, hz, lt_of_not_ge hb, h1⟩
  have href := Zeta23.zeta_reflect_zero s ⟨hz, h0, h1⟩
  have hleft := hright (Zeta23.reflect s) href.1 href.2.2
  have hr := hright s hz h1
  simp [Zeta23.reflect] at hleft
  linarith

namespace Pareto

theorem legal_error_mellin_value_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) :
    paretoMellin (hilbertOne - f) s = 1 / s := by
  have hsne : s ≠ 1 := by intro he; simp [he] at hs1
  change paretoMellinContinuous s hs (hilbertOne - f) = _
  rw [map_sub]
  change paretoMellin hilbertOne s - paretoMellin f s = _
  rw [paretoMellin_one s hs,
    paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hsne hz hf, sub_zero]

theorem legal_l1_power_barrier_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A)
    (hsmall : hilbertL1 (hilbertOne - f) ≤ 1 / (2 * ‖s‖)) :
    mellinL1Constant s ≤ ‖hilbertOne - f‖ ^ 2 *
      hilbertL1 (hilbertOne - f) ^ mellinL1Exponent s := by
  have he := legal_error_mellin_value_of_zeta A hA s hs hs1 hz hf
  exact paretoMellin_l1_power_lower _ s hs hs1 he
    (hilbertL1_pos_of_mellin_value _ s hs he) hsmall

/-- Elementary comparison of complete target-error energy with complete legal-vector energy. -/
theorem hilbert_error_energy_le (f : ThresholdHilbert) :
    ‖hilbertOne - f‖ ^ 2 ≤ 2 * (1 + ‖f‖ ^ 2) := by
  have hn := norm_sub_le hilbertOne f
  have hsq := (sq_le_sq₀ (norm_nonneg (hilbertOne - f))
    (add_nonneg (norm_nonneg hilbertOne) (norm_nonneg f))).mpr hn
  nlinarith [hilbertOne_norm_sq, sq_nonneg (‖hilbertOne‖ - ‖f‖)]

theorem riemannHypothesis_of_legal_subpower_l1
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hε : Tendsto (fun n => hilbertL1 (hilbertOne - F n)) atTop (𝓝 0))
    (hsubpower : ∀ p : ℝ, 0 < p →
      Tendsto (fun n => ‖F n‖ ^ 2 * hilbertL1 (hilbertOne - F n) ^ p)
        atTop (𝓝 0)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨s, hz, hs, hs1⟩ := exists_right_zero_of_not_RH hRH
  have hp := mellinL1Exponent_pos s hs hs1
  have hC := mellinL1Constant_pos s hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hc : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hpow : Tendsto (fun n => hilbertL1 (hilbertOne - F n) ^ mellinL1Exponent s)
      atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using hε.rpow_const (Or.inr hp.le)
  have hupper : Tendsto (fun n => 2 *
      (hilbertL1 (hilbertOne - F n) ^ mellinL1Exponent s +
      ‖F n‖ ^ 2 * hilbertL1 (hilbertOne - F n) ^ mellinL1Exponent s))
      atTop (𝓝 0) := by
    simpa using (hpow.add (hsubpower _ hp)).const_mul 2
  have hevSmall := hε.eventually_le_const (by positivity : 0 < 1 / (2 * ‖s‖))
  have hevUpper := hupper.eventually_lt_const hC
  obtain ⟨n, hnSmall, hnUpper⟩ := (hevSmall.and hevUpper).exists
  have hbar := legal_l1_power_barrier_of_zeta A hA s hs hs1 hz
    ((hilbertLegalSubspace A).le_topologicalClosure (hlegal n)) hnSmall
  have hmul := mul_le_mul_of_nonneg_right (hilbert_error_energy_le (F n))
    (Real.rpow_nonneg (hilbertL1_nonneg (hilbertOne - F n)) (mellinL1Exponent s))
  nlinarith

theorem legal_l1_energy_tendsto_atTop_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hε : Tendsto (fun n => hilbertL1 (hilbertOne - F n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖F n‖ ^ 2) atTop atTop := by
  have hp := mellinL1Exponent_pos s hs hs1
  have hC := mellinL1Constant_pos s hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hc : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hpow : Tendsto (fun n => hilbertL1 (hilbertOne - F n) ^ mellinL1Exponent s)
      atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using hε.rpow_const (Or.inr hp.le)
  have hevSmall := hε.eventually_le_const (by positivity : 0 < 1 / (2 * ‖s‖))
  apply tendsto_atTop.mpr
  intro B
  let D : ℝ := 2 * (1 + max B 0)
  have hD : 0 < D := by dsimp [D]; positivity
  have hevPow := hpow.eventually_lt_const (div_pos hC hD)
  filter_upwards [hevSmall, hevPow] with n hnSmall hnPow
  by_contra hn
  have hnB : ‖F n‖ ^ 2 < B := lt_of_not_ge hn
  have hbar := legal_l1_power_barrier_of_zeta A hA s hs hs1 hz
    ((hilbertLegalSubspace A).le_topologicalClosure (hlegal n)) hnSmall
  have hεp : 0 ≤ hilbertL1 (hilbertOne - F n) ^ mellinL1Exponent s :=
    Real.rpow_nonneg (hilbertL1_nonneg _) _
  have hmul := mul_le_mul_of_nonneg_right (hilbert_error_energy_le (F n)) hεp
  have hcoef : 2 * (1 + ‖F n‖ ^ 2) ≤ D := by
    dsimp [D]
    linarith [le_max_left B 0]
  have hmul2 := mul_le_mul_of_nonneg_right hcoef hεp
  have hstrict := (lt_div_iff₀ hD).mp hnPow
  nlinarith

theorem not_RH_legal_l1_energy_tendsto_atTop
    (hRH : ¬ RiemannHypothesis)
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hε : Tendsto (fun n => hilbertL1 (hilbertOne - F n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖F n‖ ^ 2) atTop atTop := by
  obtain ⟨s, hz, hs, hs1⟩ := exists_right_zero_of_not_RH hRH
  exact legal_l1_energy_tendsto_atTop_of_zeta A hA s hs hs1 hz F hlegal hε


end Pareto
end
end RiemannResearch.RH
