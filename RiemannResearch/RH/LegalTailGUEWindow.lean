/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GaussianDistinctRootCollision
import RiemannResearch.Analysis.GaussianDistinctRootPrecision
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.RH.LegalTailBlockOvershoot
import RiemannResearch.RH.LegalTailMeanCapacityMellin
import RiemannResearch.RH.ParetoResiduePalmSineLimit
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.RealZetaNonvanishing

/-!
# The legal fixed-window criterion and GUE repulsion

The comparison uses the reduced Palm diagonal of the unfolded Mellin model.
Its realization on actual zero pairs at absolute count accuracy is the arithmetic
obligation. A single right zero gives simultaneous lower bounds for both tests.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology ComplexConjugate
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.Analysis ActualZeroOrdinate

/-- The Gaussian benchmark integrates the exact reduced sine diagonal of the Mellin model. -/
theorem sinePalmGaussianMass_eq_mellin_palm (a : ℝ) :
    sinePalmGaussianMass a =
      ∫ x : ℝ, Real.exp (-a * x^2) * ResidueMellin.reducedSineKernel x x := by
  simp only [ResidueMellin.reducedSineKernel_diag, sinePalmGaussianMass]

private theorem rh_of_critical_cutoffs (h : ∀ T : ℝ, ∀ p ∈ cutoff T, p.re = 1 / 2) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro p hp h0 h1
  have hz : IsNontrivialZero p := ⟨hp, h0, h1⟩
  rcases lt_trichotomy 0 p.im with hi | hi | hi
  · exact h p.im p (mem_cutoff.mpr ⟨hz, hi, le_rfl⟩)
  · have he : p = (p.re : ℂ) := by apply Complex.ext <;> simp [hi.symm]
    exact False.elim (RiemannResearch.RH.riemannZeta_ofReal_ne_zero p.re h0 h1.ne
      ((congrArg riemannZeta he).symm.trans hp))
  · have hc : IsNontrivialZero (conj p) := by
      refine ⟨?_, h0, h1⟩
      rw [Zeta23.riemannZeta_conj hz.not_trivial.2, hp, map_zero]
    have hci : 0 < (conj p).im := by simpa only [Complex.conj_im] using neg_pos.mpr hi
    exact h (conj p).im (conj p) (mem_cutoff.mpr ⟨hc, hci, le_rfl⟩)

/-- The model is calibrated in absolute ordered pairs. No analytic simplicity is required. -/
theorem cofinal_sineRootGaussianTest_iff_RH :
    (∃ᶠ T : ℝ in atTop, ∃ k : ℕ, sineRootGaussianTest ((k : ℝ) + 1) T) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply rh_of_critical_cutoffs
    intro H p hp
    obtain ⟨T, htest, hHT, hT, hN⟩ :=
      (h.and_eventually ((eventually_ge_atTop H).and
        ((eventually_gt_atTop (1 : ℝ)).and eventually_count_pos))).exists
    obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hp
    exact (sineRootGaussian_finite_iff hT hN).mp htest p
      (mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩)
  · intro hrh
    apply Filter.Eventually.frequently
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_count_pos] with T hT hN
    exact (sineRootGaussian_finite_iff hT hN).mpr
      (fun p hp => RH_implies_on_line hrh (mem_cutoff.mp hp).1)

/-- Absolute GUE comparison at cofinal heights is equivalent to every fixed legal window. -/
theorem fixedBlock_liminf_zero_iff_sineRootGaussianTest :
    (∀ N : ℕ, 0 < N → liminf (fun n : ℕ =>
      negativeMassHead N (tailBlockResidual ((n + 1).factorial - 1))) atTop = 0) ↔
    (∃ᶠ T : ℝ in atTop, ∃ k : ℕ, sineRootGaussianTest ((k : ℝ) + 1) T) :=
  fixedBlock_liminf_zero_iff_RH.trans cofinal_sineRootGaussianTest_iff_RH.symm

/-- A single prescribed precision at each height suffices for the legal fixed-window test. -/
theorem fixedBlock_liminf_zero_iff_calibrated_sine_excess :
    (∀ N : ℕ, 0 < N → liminf (fun n : ℕ =>
      negativeMassHead N (tailBlockResidual ((n + 1).factorial - 1))) atTop = 0) ↔
    (∃ᶠ T : ℝ in atTop, calibratedSineRootExcess T < 1) := by
  rw [fixedBlock_liminf_zero_iff_sineRootGaussianTest]
  have he := (eventually_gt_atTop (1 : ℝ)).and eventually_count_pos
  constructor
  · intro h
    apply (h.and_eventually he).mono
    rintro T ⟨htest, hT, hN⟩
    exact (calibratedSineRootExcess_lt_one_iff hT hN).mpr
      ((sineRootGaussian_finite_iff hT hN).mp htest)
  · intro h
    apply (h.and_eventually he).mono
    rintro T ⟨htest, hT, hN⟩
    exact (sineRootGaussian_finite_iff hT hN).mpr
      ((calibratedSineRootExcess_lt_one_iff hT hN).mp htest)

/-- One specified right zero forces both a fixed legal overshoot and an absolute excess
over the sine prediction. The same window works at every legal scale. -/
theorem right_zero_forces_fixed_block_and_sine_excess {T : ℝ} {p : ℂ}
    (hp : p ∈ cutoff T) (hr : (1 / 2 : ℝ) < p.re) (hT : 1 < T)
    (K N : ℕ) (hwindow : 64 ≤ ((2*p.re - 1) / ‖p‖^2) * ((N : ℝ) + 1)) :
    ((2*p.re - 1) / ‖p‖^2) / 8 ≤ negativeMassHead N (tailBlockResidual K) ∧
    2 * (zeroMult p : ℝ)^2 - 3 / 8 ≤ calibratedSineRootExcess T := by
  have hcount : 0 < Ncount 0 T := by
    rw [count_eq_sum]
    exact lt_of_lt_of_le (multiplicity_pos hp)
      (Finset.single_le_sum (fun z _ => Nat.zero_le (zeroMult z)) hp)
  have hz := (mem_cutoff.mp hp).1
  have hp0 : p ≠ 0 := by intro he; simp [he] at hr; linarith
  have hp1 : p ≠ 1 := by intro he; have h := hz.2.2; simp [he] at h
  have hgap : 0 < (2*p.re - 1) / ‖p‖^2 :=
    div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hp0))
  have hδ : (2*p.re - 1) / ‖p‖^2 ≤ tailCapacityDeficit K := by
    have h := legalTailMeanCapacity_zero_gap K p hr hp1 hz.1
    change _ ≤ 1 - (((K : ℝ) + 1) * legalTailMeanCapacity K)
    linarith
  refine ⟨(div_le_div_of_nonneg_right hδ (by norm_num)).trans
    (tailBlockOvershoot_finite_window hgap hδ hwindow), ?_⟩
  have hfloor : 2 * (zeroMult p : ℝ)^2 ≤ (distinctRootCollisionCount T : ℝ) := by
    exact_mod_cast reflected_pair_le_distinctRootCollision hp (ne_of_gt hr)
  have he := (abs_le.mp (calibratedSineRootExcess_error hT hcount)).1
  linarith only [hfloor, he]

end RiemannResearch.RH.Pareto.PrimePowerSchur
