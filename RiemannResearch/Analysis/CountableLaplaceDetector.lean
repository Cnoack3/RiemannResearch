import RiemannResearch.Analysis.BilateralLaplaceEntire
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
Source: user-provided countable-tilt argument preserved in
RH_Lean_Continuation_2026-09-09.zip (statement and proof strategy).

This route constructs smooth compact tests detecting a specified countable
set. It does NOT assert transform nonvanishing at every point of a strip,
and does NOT replace the infinite-convolution construction with that claim.

The selected spectrum must be countable; no growth estimate is asserted.
-/

noncomputable section
open MeasureTheory
open scoped Topology

namespace RiemannResearch.Analysis

theorem countable_zeros_of_entire_nonzero {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H Set.univ) {z₀ : ℂ} (h₀ : H z₀ ≠ 0) :
    {z : ℂ | H z = 0}.Countable := by
  have hc : {z : ℂ | H z = 0}ᶜ ∈ Filter.codiscrete ℂ := by
    exact hH.preimage_zero_mem_codiscrete h₀
  have hd : IsDiscrete {z : ℂ | H z = 0} :=
    (compl_mem_codiscrete_iff.mp hc).2
  let : DiscreteTopology {z : ℂ | H z = 0} :=
    isDiscrete_iff_discreteTopology.mp hd
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

/-- Countable spectra can be simultaneously avoided by one real shift. -/
theorem exists_real_shift_avoiding_countable_zeros
    {S : Set ℂ} (hS : S.Countable) {H : ℂ → ℂ}
    (hZ : {z : ℂ | H z = 0}.Countable) :
    ∃ c : ℝ, ∀ s ∈ S, H (s - (c : ℂ)) ≠ 0 := by
  let B : Set ℝ := (fun p : ℂ × ℂ => (p.1 - p.2).re) ''
    (S ×ˢ {z : ℂ | H z = 0})
  have hB : B.Countable := (hS.prod hZ).image _
  have he : ∃ c : ℝ, c ∉ B := by
    by_contra hn
    push Not at hn
    have hu : B = Set.univ := Set.eq_univ_of_forall hn
    exact Set.not_countable_univ (hu ▸ hB)
  obtain ⟨c, hc⟩ := he
  refine ⟨c, fun s hs hz => hc ?_⟩
  refine ⟨(s, s - (c : ℂ)), ⟨hs, hz⟩, ?_⟩
  simp

theorem exists_real_shift_detecting_countable_set
    {S : Set ℂ} (hS : S.Countable) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H Set.univ) {z₀ : ℂ} (h₀ : H z₀ ≠ 0) :
    ∃ c : ℝ, ∀ s ∈ S, H (s - (c : ℂ)) ≠ 0 :=
  exists_real_shift_avoiding_countable_zeros hS
    (countable_zeros_of_entire_nonzero hH h₀)

/-- A genuine exponential tilt of a spatial test. -/
def exponentialTilt (c : ℝ) (h : ℝ → ℂ) (y : ℝ) : ℂ :=
  Complex.exp ((c : ℂ) * (y : ℂ)) * h y

theorem exponentialTilt_contDiff (c : ℝ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (exponentialTilt c h) := by
  unfold exponentialTilt
  exact ((Complex.contDiff_exp.comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hh)

theorem exponentialTilt_hasCompactSupport (c : ℝ) {h : ℝ → ℂ}
    (hh : HasCompactSupport h) : HasCompactSupport (exponentialTilt c h) :=
  hh.mul_left

theorem centeredTransform_exponentialTilt (c : ℝ) (h : ℝ → ℂ) (s : ℂ) :
    BilateralLaplace.centeredTransform (exponentialTilt c h) s =
      BilateralLaplace.centeredTransform h (s - (c : ℂ)) := by
  unfold BilateralLaplace.centeredTransform BilateralLaplace.transform
    BilateralLaplace.kernel exponentialTilt
  apply integral_congr_ae
  filter_upwards [] with y
  calc
    (Complex.exp ((c : ℂ) * (y : ℂ)) * h y) *
        Complex.exp (-(s - 1 / 2) * (y : ℂ)) =
        h y * (Complex.exp ((c : ℂ) * (y : ℂ)) *
          Complex.exp (-(s - 1 / 2) * (y : ℂ))) := by ring
    _ = h y * Complex.exp ((c : ℂ) * (y : ℂ) +
          -(s - 1 / 2) * (y : ℂ)) := by rw [Complex.exp_add]
    _ = h y * Complex.exp (-(s - (c : ℂ) - 1 / 2) * (y : ℂ)) := by
      congr 2
      ring

/-- An actual normalized nonnegative compact bump, independent of the spectrum. -/
def detectorBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def detectorSeed (y : ℝ) : ℂ := (detectorBump.normed volume y : ℂ)

theorem detectorSeed_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) detectorSeed :=
  Complex.ofRealCLM.contDiff.comp detectorBump.contDiff_normed

theorem detectorSeed_hasCompactSupport : HasCompactSupport detectorSeed := by
  exact detectorBump.hasCompactSupport_normed.comp_left (by simp)

theorem centeredTransform_detectorSeed_half :
    BilateralLaplace.centeredTransform detectorSeed (1 / 2) = 1 := by
  simp only [BilateralLaplace.centeredTransform, BilateralLaplace.transform,
    BilateralLaplace.kernel, sub_self, neg_zero, zero_mul, Complex.exp_zero,
    mul_one, detectorSeed]
  simpa only [Complex.real_smul, mul_one] using
    detectorBump.integral_normed_smul volume (1 : ℂ)

/-- Actual smooth compact seed detecting every member of a countable set.
The RH application is assembled in RH/CountableTiltDetector.lean. -/
theorem exists_smooth_compact_countable_detector
    {S : Set ℂ} (hS : S.Countable) :
    ∃ v : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      ∀ s ∈ S, BilateralLaplace.centeredTransform v s ≠ 0 := by
  have hm := BilateralLaplace.hasExponentialMoments_of_compactSupport
    detectorSeed_contDiff.continuous detectorSeed_hasCompactSupport
  have hH : AnalyticOnNhd ℂ (BilateralLaplace.centeredTransform detectorSeed)
      Set.univ := fun s _ => BilateralLaplace.analyticAt_centeredTransform hm s
  have h₀ : BilateralLaplace.centeredTransform detectorSeed (1 / 2) ≠ 0 := by
    rw [centeredTransform_detectorSeed_half]
    norm_num
  obtain ⟨c, hc⟩ := exists_real_shift_detecting_countable_set hS hH h₀
  refine ⟨exponentialTilt c detectorSeed,
    exponentialTilt_contDiff c detectorSeed_contDiff,
    exponentialTilt_hasCompactSupport c detectorSeed_hasCompactSupport, ?_⟩
  intro s hs
  rw [centeredTransform_exponentialTilt]
  exact hc s hs

end RiemannResearch.Analysis
