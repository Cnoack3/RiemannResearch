import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.Analysis.MellinTransform

/-!
# Holomorphy of the actual bounded-sequence Pareto Mellin integral

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. Analytic method: Mathlib's Mellin-transform differentiability
theorem, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MellinTransform.html.
The actual physical step is measurable, bounded, and zero near zero.
Consequently its Mellin integral is holomorphic for Re(s)>0, including
the entire continuity half-plane needed for arithmetic continuation.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

private def cutoffMellinStep (f : ThresholdHilbert) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x => (hilbertSequence f ⌊x⌋₊ : ℂ))

private theorem cutoffMellinStep_measurable (f : ThresholdHilbert) :
    Measurable (cutoffMellinStep f) := by
  have hf : Measurable (fun x : ℝ => hilbertSequence f ⌊x⌋₊) :=
    (measurable_of_countable (hilbertSequence f)).comp Nat.measurable_floor
  exact (Complex.continuous_ofReal.measurable.comp hf).indicator measurableSet_Ioi

private theorem cutoffMellinStep_bound (f : ThresholdHilbert) {C : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ C) (x : ℝ) :
    ‖cutoffMellinStep f x‖ ≤ C := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · simpa only [cutoffMellinStep, Set.indicator_of_mem hx,
      Complex.norm_real, Real.norm_eq_abs] using hf ⌊x⌋₊
  · have hC : 0 ≤ C := (abs_nonneg (hilbertSequence f 0)).trans (hf 0)
    simpa only [cutoffMellinStep, Set.indicator_of_notMem hx, norm_zero] using hC

private theorem cutoffMellinStep_locallyIntegrable (f : ThresholdHilbert) {C : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ C) :
    LocallyIntegrableOn (cutoffMellinStep f) (Ioi (0 : ℝ)) := by
  apply (locallyIntegrableOn_const (X := ℝ) (μ := volume)
    (s := Ioi (0 : ℝ)) C).mono
      ((cutoffMellinStep_measurable f).aestronglyMeasurable (μ := volume))
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using
      (cutoffMellinStep_bound f hf x).trans (le_abs_self C)

private theorem cutoffMellinStep_isBigO_top (f : ThresholdHilbert) {C : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ C) :
    Asymptotics.IsBigO atTop (cutoffMellinStep f) (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound C
  exact Eventually.of_forall fun x => by
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
      cutoffMellinStep_bound f hf x

private theorem cutoffMellinStep_isBigO_zero (f : ThresholdHilbert) (b : ℝ) :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ)) (cutoffMellinStep f)
      (fun x : ℝ => x ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have hnear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [hnear] with x hx
  change x < 1 at hx
  have hx' : x ∉ Ioi (1 : ℝ) := by
    exact not_lt.mpr (le_of_lt hx)
  simp [cutoffMellinStep, hx']

private theorem paretoMellin_eq_cutoff_mellin (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin f s = mellin (cutoffMellinStep f) (-s) := by
  rw [paretoMellin_eq_step_integral]
  calc
    _ = ∫ x in Ioi (1 : ℝ), cutoffMellinStep f x * (x : ℂ) ^ (-s - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [cutoffMellinStep, Set.indicator_of_mem hx]
    _ = ∫ x, cutoffMellinStep f x * (x : ℂ) ^ (-s - 1) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [cutoffMellinStep, Set.indicator_of_notMem hx, zero_mul]
    _ = ∫ x in Ioi (0 : ℝ), cutoffMellinStep f x * (x : ℂ) ^ (-s - 1) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : x ∉ Ioi (1 : ℝ) := by
        have hx0 : x ≤ 0 := not_lt.mp hx
        exact not_lt.mpr (hx0.trans zero_le_one)
      simp only [cutoffMellinStep, Set.indicator_of_notMem hx', zero_mul]
    _ = _ := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      simp only [smul_eq_mul, mul_comm]

/-- Actual bounded physical sequences give a holomorphic Mellin integral on
the whole open half-plane Re(s)>0, without an arithmetic hypothesis. -/
theorem paretoMellin_differentiableAt_of_bounded (f : ThresholdHilbert) {C : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ C) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (paretoMellin f) s := by
  have h := mellin_differentiableAt_of_isBigO_rpow
    (cutoffMellinStep_locallyIntegrable f hf)
    (cutoffMellinStep_isBigO_top f hf)
    (s := -s) (by simp only [Complex.neg_re]; linarith)
    (cutoffMellinStep_isBigO_zero f (-s.re - 1))
    (by simp only [Complex.neg_re]; linarith)
  have he : paretoMellin f = fun z => mellin (cutoffMellinStep f) (-z) := by
    funext z
    exact paretoMellin_eq_cutoff_mellin f z
  rw [he]
  exact h.comp s differentiableAt_id.neg

theorem paretoMellin_differentiableOn_of_bounded (f : ThresholdHilbert) {C : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ C) :
    DifferentiableOn ℂ (paretoMellin f) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (paretoMellin_differentiableAt_of_bounded f hf s hs).differentiableWithinAt

end
end RiemannResearch.RH.Pareto
