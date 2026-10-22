import RiemannResearch.RH.ParetoMellinHeadObstruction
import RiemannResearch.RH.ParetoL1MellinBound
import RiemannResearch.RH.ThresholdRiemannHypothesis

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.RH.Pareto

/- Source: user-provided Green--Pareto--Schur continuation, 6 October 2026,
Sections 23 and 25 (statements and localized Mellin proof strategy). -/

/-- Direct specialization of two existing actual analytic theorems.
No Mellin detector is assumed as an arithmetic provider. -/
theorem legal_exact_head_power_lower
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A)
    {N : ℕ} (hN : 3 ≤ N)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
      ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ ‖f‖ ^ 2 := by
  exact paretoMellin_exact_head_power_lower hN hhead s hs
    (paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf)

/-- An actual vector whose physical head vanishes has a localized Mellin bound.
This proves the support-dependent detector from the existing tail Cauchy theorem. -/
theorem mellin_zero_head_lower
    (e : ThresholdHilbert) (n : ℕ) (hn : 1 ≤ n)
    (hhead : ∀ k, 0 < k → k < n → hilbertSequence e k = 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (2 * s.re - 1) * ‖paretoMellin e s‖ ^ 2 *
      (n : ℝ) ^ (2 * s.re - 1) ≤ ‖e‖ ^ 2 := by
  have hb : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb0 : (0 : ℝ) < n := by linarith
  have hh : (∫ x in (1 : ℝ)..(n : ℝ),
      mellinWeightedStep e x * paretoMellinKernel s x) = 0 := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Ico_eq_integral_Ioc]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx.1
    have hlo : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx.1)
    have hhi : ⌊x⌋₊ < n := (Nat.floor_lt hx0).2 (by exact_mod_cast hx.2)
    simp [mellinWeightedStep, hhead _ (by omega) hhi]
  have hfull := paretoMellin_integrable e s hs
  have htail := hfull.mono_set (Ioi_subset_Ioi hb)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  change (∫ x in (1 : ℝ)..(n : ℝ),
      mellinWeightedStep e x * paretoMellinKernel s x) +
    (∫ x in Ioi (n : ℝ), mellinWeightedStep e x * paretoMellinKernel s x) =
      paretoMellin e s at hsplit
  have htval : (∫ x in Ioi (n : ℝ),
      mellinWeightedStep e x * paretoMellinKernel s x) = paretoMellin e s := by
    simpa only [hh, zero_add] using hsplit
  have ht := paretoMellin_tail_full_energy_bound e s hs hb
  rw [htval] at ht
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hp : 0 < (n : ℝ) ^ (2 * s.re - 1) := Real.rpow_pos_of_pos hb0 _
  have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg hd.le hp.le)
  have hexp : (n : ℝ) ^ (1 - 2 * s.re) =
      ((n : ℝ) ^ (2 * s.re - 1))⁻¹ := by
    rw [show 1 - 2 * s.re = -(2 * s.re - 1) by ring,
      Real.rpow_neg hb0.le]
  rw [hexp] at hm
  have hr : (2 * s.re - 1) * (n : ℝ) ^ (2 * s.re - 1) *
      (‖e‖ ^ 2 * (((n : ℝ) ^ (2 * s.re - 1))⁻¹ / (2 * s.re - 1))) =
      ‖e‖ ^ 2 := by
    field_simp [hd.ne', hp.ne']
  rw [hr] at hm
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

/-- Sharp actual legal residual obstruction; the zeta-zero Mellin value
is derived from the existing legal-space theorem, not assumed. -/
theorem legal_exact_head_residual_power_lower
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A)
    (n : ℕ) (hn : 1 ≤ n)
    (hhead : ∀ k, 0 < k → k < n → hilbertSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) *
      (n : ℝ) ^ (2 * s.re - 1) ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf
  have heval : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have hehead : ∀ k, 0 < k → k < n →
      hilbertSequence (hilbertOne - f) k = 0 := by
    intro k hk hkn
    change hilbertSequenceLinear (hilbertOne - f) k = 0
    rw [map_sub]
    change hilbertSequence hilbertOne k - hilbertSequence f k = 0
    rw [hilbertOne_sequence, hhead k hk hkn]
    simp [zeroAnchor, ne_of_gt hk]
  have h := mellin_zero_head_lower (hilbertOne - f) n hn hehead s hs
  rw [heval, norm_div, norm_one, div_pow, one_pow] at h
  convert h using 1
  ring

end RiemannResearch.RH.Pareto
