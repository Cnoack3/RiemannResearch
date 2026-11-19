/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.XiLogDerivativeDisk
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# A countable Taylor-series test for RH

Every strictly smaller radius at every rational center suffices. Cauchy's
integral supplies the series on the forward implication. The converse uses
analyticity wherever a given series represents the function in its open disk.
-/

noncomputable section
open Metric Set Zeta23.XiPrime Complex
open scoped NNReal ENNReal
namespace RiemannResearch.RH.RationalZeroFreeDisks

def diskCenter (q : ℚ) : ℂ := ⟨1, (q:ℝ)⟩

theorem rationalOpenDisk_eq_ball (q : ℚ) {r : ℝ} (hr : 0 ≤ r) :
    rationalOpenDisk q r = Metric.ball (diskCenter q) r := by
  ext z
  change ((1-z.re)^2+((q:ℝ)-z.im)^2 < r^2) ↔ dist z (diskCenter q) < r
  rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, diskCenter]
  constructor <;> intro h <;> nlinarith only [h]

def RationalTaylorDisks (R : ℝ) : Prop :=
  ∀ (q r : ℚ), 0 < (r:ℝ) → (r:ℝ) < R →
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesOnBall (logDeriv xi) p (diskCenter q) (ENNReal.ofReal (r:ℝ))

theorem taylorDisks_iff_analytic_disks {R : ℝ} (hR : 0 ≤ R) :
    RationalTaylorDisks R ↔
      ∀ q : ℚ, AnalyticOnNhd ℂ (logDeriv xi) (rationalOpenDisk q R) := by
  constructor
  · intro h q z hz
    rw [rationalOpenDisk_eq_ball q hR] at hz
    obtain ⟨s, hds, hsR⟩ := exists_rat_btwn (Metric.mem_ball.mp hz)
    have hs : 0 < (s:ℝ) := (dist_nonneg : 0 ≤ dist z (diskCenter q)).trans_lt hds
    obtain ⟨p, hp⟩ := h q s hs hsR
    apply hp.analyticAt_of_mem
    change edist z (diskCenter q) < ENNReal.ofReal (s:ℝ)
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hs).mpr hds
  · intro h q r hr hrR
    let rad : ℝ≥0 := ⟨(r:ℝ),hr.le⟩
    have hdr : 0 < rad := hr
    have hd : DifferentiableOn ℂ (logDeriv xi) (Metric.closedBall (diskCenter q) (rad:ℝ)) := by
      intro z hz
      have hdist := (Metric.mem_closedBall.mp hz).trans_lt hrR
      apply ((h q z _).differentiableAt).differentiableWithinAt
      rw [rationalOpenDisk_eq_ball q hR]
      exact Metric.mem_ball.mpr hdist
    have he : ENNReal.ofReal (r:ℝ) = (rad : ℝ≥0∞) := by
      change ENNReal.ofReal (rad:ℝ) = (rad:ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rw [he]
    exact ⟨_, hd.hasFPowerSeriesOnBall hdr⟩

theorem riemannHypothesis_iff_rationalTaylorDisks :
    RiemannHypothesis ↔ RationalTaylorDisks (1/2) :=
  riemannHypothesis_iff_xi_logDerivative_disks.trans
    (taylorDisks_iff_analytic_disks (by norm_num)).symm

end RiemannResearch.RH.RationalZeroFreeDisks
