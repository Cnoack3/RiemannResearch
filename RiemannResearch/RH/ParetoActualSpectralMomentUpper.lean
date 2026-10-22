/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoActualSpectralLimits
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.Analysis.FiniteSpectralMomentUpper

/-!
# Arithmetic conductor caps and complete-source double-log upper bounds

Source: user-provided complete-source spectral budget task, 7 October 2026.
The published full-tail Mobius repair discharges the stage eigenvalue cap.
Every actual source weight and eigenvalue is retained. The final consumer
still requires the explicitly displayed arithmetic cap-contrast estimate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
open FiniteSpectralBudget FiniteHeadTailSpectralRealization

private theorem stage_compactHead_comp_of_le (n N : ℕ) (h : n ≤ N)
    (f : ThresholdHilbert) :
    compactHead n (compactHead N f) = compactHead n f := by
  apply hilbertSequence_injective
  funext j
  by_cases hj : j ≤ n
  · simp [compactHead_sequence, hj, le_trans hj h]
  · simp [compactHead_sequence, hj]

/-- Arithmetic conditioning of the actual inverse head restriction, over
the full infinite physical space and the entire legal conductor stage. -/
theorem stageHeadLift_norm_le_conductor (n N : ℕ) (hN : n + 1 ≤ N)
    (x : stageHeadSpace n N) :
    ‖stageHeadLift n N hN x‖ ≤ 12 * (n : ℝ) * ‖x‖ := by
  have hq : ‖compactHead n (stageHeadLift n N hN x)‖ ≤
      ‖(x : ThresholdHilbert)‖ := by
    have h := compactHead_norm_le n (compactHead N (stageHeadLift n N hN x))
    rw [stage_compactHead_comp_of_le n N (by omega),
      compactHead_stageHeadLift] at h
    exact h
  calc
    _ ≤ 12 * (n : ℝ) * ‖compactHead n (stageHeadLift n N hN x)‖ :=
      finiteSpace_norm_le_head n _ (stageHeadLift_mem n N hN x)
    _ ≤ 12 * (n : ℝ) * ‖x‖ := mul_le_mul_of_nonneg_left hq (by positivity)

/-- Explicit conductor cap for EVERY eigenvalue; the orthogonal head square
one is retained before bounding the tail square. -/
theorem stageEigenvalue_le_conductor_cap (n N : ℕ) (hN : n + 1 ≤ N)
    (i : Fin (Module.finrank ℝ (stageHeadSpace n N))) :
    stageEigenvalue n N hN i ≤ 144 * (n : ℝ) ^ 2 - 1 := by
  have hb := orthonormal_iff_ite.mp (stageEigenBasis n N hN).orthonormal i i
  rw [if_pos rfl, real_inner_self_eq_norm_sq] at hb
  have hb1 : ‖stageEigenBasis n N hN i‖ = 1 := by
    nlinarith [norm_nonneg (stageEigenBasis n N hN i)]
  have hn := stageHeadLift_norm_le_conductor n N hN (stageEigenBasis n N hN i)
  rw [hb1, mul_one] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 12 * (n : ℝ))).mpr hn
  have hp := compactHead_pythagoras N
    (stageHeadLift n N hN (stageEigenBasis n N hN i))
  rw [compactHead_stageHeadLift] at hp
  have ht := tail_basis_inner (stageTailLift n N hN) i i
  rw [if_pos rfl, real_inner_self_eq_norm_sq,
    stageTailLift_eq_physicalTail, compactHead_stageHeadLift] at ht
  change ‖stageHeadLift n N hN (stageEigenBasis n N hN i)‖ ^ 2 =
    ‖stageEigenBasis n N hN i‖ ^ 2 +
      ‖stageHeadLift n N hN (stageEigenBasis n N hN i) -
        (stageEigenBasis n N hN i : ThresholdHilbert)‖ ^ 2 at hp
  rw [hb, ht] at hp
  nlinarith only [hs,hp]

def compactSpectrumConductorCap (n : ℕ) : ℝ := 144 * ((n : ℝ) + 3) ^ 2 - 1

theorem compactSpectrumEigenvalue_le_conductor_cap (n : ℕ)
    (i : compactSpectrumIndex n) :
    compactSpectrumEigenvalue n i ≤ compactSpectrumConductorCap n := by
  simpa only [compactSpectrumEigenvalue, compactSpectrumConductorCap,
    Nat.cast_add, Nat.cast_ofNat] using
    stageEigenvalue_le_conductor_cap (n + 3) (n + 4) (by omega) i

/-- Exact compact source normalization, evaluated at all three physical sites. -/
theorem twoThreeDual_norm_sq_eq_134 : ‖twoThreeDual‖^2 = 134 := by
  rw [← compactHead_twoThreeDual 3 (by decide),
    compactHead_norm_sq_eq_physical_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp_rw [hilbertGibbsPhysical_eq, twoThreeDual_sequence]
  norm_num [compactStepTarget, paretoWeight]

/-- Total mass is identified exactly, before using the uniform cap 134. -/
theorem compactSpectrum_mass_eq_134_sub_headError (n : ℕ) :
    mass Finset.univ (compactSpectrumWeight n) =
      134 - ‖twoThreeDual -
        (stageHeadSpace (n+3) (n+4)).starProjection twoThreeDual‖^2 := by
  simpa only [compactSpectrumWeight, twoThreeDual_norm_sq_eq_134] using
    actualSourceMass_eq_targetNorm_sub_headError (n+3) (n+4) (by omega) twoThreeDual

theorem compactSpectrum_mass_le_134 (n : ℕ) :
    mass Finset.univ (compactSpectrumWeight n) ≤ 134 := by
  rw [compactSpectrum_mass_eq_134_sub_headError]
  linarith [sq_nonneg ‖twoThreeDual -
    (stageHeadSpace (n+3) (n+4)).starProjection twoThreeDual‖]

theorem compactSpectrum_mass_tendsto_134 :
    Tendsto (fun n => mass Finset.univ (compactSpectrumWeight n)) atTop (𝓝 134) := by
  simpa only [compactSpectrum_mass_eq_134_sub_headError, sub_zero] using
    (tendsto_const_nhds.sub twoThree_actualHeadError_tendsto_zero)

def compactSpectrumDoubleLogRemainder (n : ℕ) : ℝ :=
  doubleLogRemainder Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n)

def compactSpectrumDoubleLogContrast (n : ℕ) : ℝ :=
  doubleLogCapContrast Finset.univ (compactSpectrumWeight n)
    (compactSpectrumEigenvalue n) (compactSpectrumConductorCap n)

def compactSpectrumDoubleLogScale (n : ℕ) : ℝ :=
  Real.log (1+Real.log (1/compactSpectrumTailEnvelope n))

theorem compactSpectrum_doubleLog_exact_contrast (n : ℕ) :
    moment Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) doubleLog =
      doubleLog (compactSpectrumConductorCap n) *
        correction Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) -
      compactSpectrumDoubleLogContrast n + compactSpectrumDoubleLogRemainder n :=
  moment_eq_cap_correction_sub_contrast_add_remainder _ _ _ _
    (fun i _ => compactSpectrumEigenvalue_nonneg n i)

theorem compactSpectrumDoubleLogContrast_nonneg (n : ℕ) :
    0 ≤ compactSpectrumDoubleLogContrast n :=
  doubleLogCapContrast_nonneg _ _ _ _
    (fun i _ => compactSpectrumWeight_nonneg n i)
    (fun i _ => compactSpectrumEigenvalue_nonneg n i)
    (fun i _ => compactSpectrumEigenvalue_le_conductor_cap n i)

theorem compactSpectrumDoubleLogRemainder_le_sqrt_tail (n : ℕ) :
    compactSpectrumDoubleLogRemainder n ≤
      Real.sqrt (134 * optimizerTail Finset.univ
        (compactSpectrumWeight n) (compactSpectrumEigenvalue n)) := by
  have h := doubleLogRemainder_le_sqrt_mass_tail Finset.univ
    (compactSpectrumWeight n) (compactSpectrumEigenvalue n)
    (fun i _ => compactSpectrumWeight_nonneg n i)
    (fun i _ => compactSpectrumEigenvalue_nonneg n i)
  exact h.trans (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right (compactSpectrum_mass_le_134 n)
      (optimizerTail_nonneg _ _ _ (fun i _ => compactSpectrumWeight_nonneg n i)
        (fun i _ => compactSpectrumEigenvalue_nonneg n i))))

theorem compactSpectrumDoubleLogRemainder_tendsto_zero :
    Tendsto compactSpectrumDoubleLogRemainder atTop (𝓝 0) := by
  have hs := compactSpectrum_optimizerTail_tendsto_zero.const_mul 134
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [mul_zero, Real.sqrt_zero, Function.comp_def] at hroot
  exact squeeze_zero
    (fun n => doubleLogRemainder_nonneg _ _ _
      (fun i _ => compactSpectrumWeight_nonneg n i)
      (fun i _ => compactSpectrumEigenvalue_nonneg n i))
    compactSpectrumDoubleLogRemainder_le_sqrt_tail hroot

/-- Unconditional full-source upper bound: leading correction T rather than
total mass 134, with a cap-independent vanishing remainder and exact credit. -/
theorem compactSpectrum_doubleLog_upper_with_contrast (n : ℕ) :
    moment Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) doubleLog ≤
      doubleLog (compactSpectrumConductorCap n) *
        correction Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) -
      compactSpectrumDoubleLogContrast n +
      Real.sqrt (134 * optimizerTail Finset.univ
        (compactSpectrumWeight n) (compactSpectrumEigenvalue n)) := by
  rw [compactSpectrum_doubleLog_exact_contrast]
  exact add_le_add le_rfl (compactSpectrumDoubleLogRemainder_le_sqrt_tail n)

theorem compactSpectrumDoubleLogScale_tendsto_atTop :
    Tendsto compactSpectrumDoubleLogScale atTop atTop := by
  have hwithin : Tendsto compactSpectrumTailEnvelope atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨compactSpectrumTailEnvelope_tendsto_zero,
      Filter.Eventually.of_forall compactSpectrumTailEnvelope_pos⟩
  have hinv : Tendsto (fun n => 1 / compactSpectrumTailEnvelope n) atTop atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hwithin
  have hlog := Real.tendsto_log_atTop.comp hinv
  have hinner : Tendsto (fun n => 1 + Real.log (1 / compactSpectrumTailEnvelope n))
      atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hlog.eventually (eventually_ge_atTop (b - 1))] with n hn
    dsimp only [Function.comp_def] at hn
    linarith
  exact Real.tendsto_log_atTop.comp hinner

theorem compactSpectrum_normalized_doubleLogRemainder_tendsto_zero :
    Tendsto (fun n => compactSpectrumDoubleLogRemainder n /
      compactSpectrumDoubleLogScale n) atTop (𝓝 0) :=
  compactSpectrumDoubleLogRemainder_tendsto_zero.div_atTop
    compactSpectrumDoubleLogScale_tendsto_atTop

/-- The SINGLE unresolved arithmetic estimate is a lower bound for the
literal complete cap contrast. All geometric and remainder estimates above
are discharged. The error may tend to zero at any rate, on a cofinal sequence. -/
theorem riemannHypothesis_of_actual_compactSpectrum_cofinal_contrast
    (k : ℕ → ℕ) (E : ℕ → ℝ) (theta : ℝ)
    (hk : Tendsto k atTop atTop) (htheta : theta < 1)
    (hE : Tendsto E atTop (𝓝 0))
    (hcontrast : ∀ᶠ n in atTop,
      (doubleLog (compactSpectrumConductorCap (k n)) -
        theta * compactSpectrumDoubleLogScale (k n)) *
        correction Finset.univ (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n)) ≤
      compactSpectrumDoubleLogContrast (k n) +
        compactSpectrumDoubleLogScale (k n) * E n) : RiemannHypothesis := by
  let F : ℕ → ℝ := fun n => E n +
    compactSpectrumDoubleLogRemainder (k n) / compactSpectrumDoubleLogScale (k n)
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [F, Function.comp_def, add_zero] using hE.add
      (compactSpectrum_normalized_doubleLogRemainder_tendsto_zero.comp hk)
  apply riemannHypothesis_of_actual_compactSpectrum_cofinal_canonical_feedback k F theta
    hk htheta hF
  have hpos : ∀ᶠ n in atTop, 0 < compactSpectrumDoubleLogScale (k n) :=
    (compactSpectrumDoubleLogScale_tendsto_atTop.comp hk).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hcontrast,hpos] with n hn hD
  change _ / compactSpectrumDoubleLogScale (k n) ≤ _
  apply (div_le_iff₀ hD).mpr
  rw [compactSpectrum_doubleLog_exact_contrast]
  dsimp [F]
  have hid : (compactSpectrumDoubleLogRemainder (k n) /
      compactSpectrumDoubleLogScale (k n)) * compactSpectrumDoubleLogScale (k n) =
        compactSpectrumDoubleLogRemainder (k n) := div_mul_cancel₀ _ (ne_of_gt hD)
  nlinarith only [hn,hid]

/-- Natural conductor double-log scale, distinct from the literal canonical
physical-tail scale whose rate is not presumed. -/
def compactSpectrumConductorLogScale (n : ℕ) : ℝ :=
  Real.log (1 + Real.log ((n : ℝ) + 3))

theorem compactSpectrumConductorLogScale_pos (n : ℕ) :
    0 < compactSpectrumConductorLogScale n := by
  unfold compactSpectrumConductorLogScale
  have hx : 1 < (n : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  exact Real.log_pos (by linarith [Real.log_pos hx])

/-- A polynomial conductor cap changes the outer log by only a bounded
additive amount; decreasing a polynomial exponent cannot give theta < 1. -/
theorem compactSpectrum_conductor_cap_doubleLog_bounds (n : ℕ) :
    compactSpectrumConductorLogScale n ≤ doubleLog (compactSpectrumConductorCap n) ∧
      doubleLog (compactSpectrumConductorCap n) ≤
        compactSpectrumConductorLogScale n + Real.log (3 + Real.log 144) := by
  have hx : 0 < (n : ℝ) + 3 := by positivity
  have hu : 0 ≤ Real.log ((n : ℝ) + 3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc : 0 ≤ Real.log (144 : ℝ) := Real.log_nonneg (by norm_num)
  have he : doubleLog (compactSpectrumConductorCap n) =
      Real.log (1 + Real.log 144 + 2 * Real.log ((n : ℝ) + 3)) := by
    unfold doubleLog compactSpectrumConductorCap
    have halg : 1 + (144 * ((n : ℝ) + 3) ^ 2 - 1) =
        144 * ((n : ℝ) + 3) ^ 2 := by ring
    rw [halg, Real.log_mul (by norm_num : (144 : ℝ) ≠ 0)
      (by positivity : ((n : ℝ) + 3) ^ 2 ≠ 0), Real.log_pow]
    congr 1
    ring
  rw [he]
  constructor
  · exact Real.log_le_log (by linarith : 0 < 1 + Real.log ((n : ℝ) + 3))
      (by nlinarith only [hc, hu])
  · have hinside : 1 + Real.log 144 + 2 * Real.log ((n : ℝ) + 3) ≤
        (3 + Real.log 144) * (1 + Real.log ((n : ℝ) + 3)) := by
      nlinarith [mul_nonneg hc hu]
    have h := Real.log_le_log (by linarith : 0 < 1 + Real.log 144 +
      2 * Real.log ((n : ℝ) + 3)) hinside
    rw [Real.log_mul (by linarith : 3 + Real.log (144 : ℝ) ≠ 0)
      (by linarith : 1 + Real.log ((n : ℝ) + 3) ≠ 0)] at h
    dsimp [compactSpectrumConductorLogScale]
    linarith

theorem compactSpectrumConductorLogScale_tendsto_atTop :
    Tendsto compactSpectrumConductorLogScale atTop atTop := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop (b - 3))] with n hn
    linarith
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hi : Tendsto (fun n : ℕ => 1 + Real.log ((n : ℝ) + 3)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hl.eventually (eventually_ge_atTop (b - 1))] with n hn
    linarith
  exact Real.tendsto_log_atTop.comp hi

theorem compactSpectrum_cap_doubleLog_scale_ratio_tendsto_one :
    Tendsto (fun n => doubleLog (compactSpectrumConductorCap n) /
      compactSpectrumConductorLogScale n) atTop (𝓝 1) := by
  have hdiff : Tendsto (fun n => (doubleLog (compactSpectrumConductorCap n) -
      compactSpectrumConductorLogScale n) / compactSpectrumConductorLogScale n)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg (sub_nonneg.mpr (compactSpectrum_conductor_cap_doubleLog_bounds n).1)
        (compactSpectrumConductorLogScale_pos n).le
    · intro n
      exact div_le_div_of_nonneg_right
        (show doubleLog (compactSpectrumConductorCap n) - compactSpectrumConductorLogScale n ≤
          Real.log (3 + Real.log 144) by
          linarith [(compactSpectrum_conductor_cap_doubleLog_bounds n).2])
        (compactSpectrumConductorLogScale_pos n).le
    · exact tendsto_const_nhds.div_atTop compactSpectrumConductorLogScale_tendsto_atTop
  have hid (n : ℕ) : doubleLog (compactSpectrumConductorCap n) /
      compactSpectrumConductorLogScale n =
      1 + (doubleLog (compactSpectrumConductorCap n) -
        compactSpectrumConductorLogScale n) / compactSpectrumConductorLogScale n := by
    field_simp [ne_of_gt (compactSpectrumConductorLogScale_pos n)]
    ring
  simpa only [hid, add_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hdiff

/-- Unconditional endpoint upper floor with the limiting actual defect as
coefficient, not the total source mass. No normalized moment limit is assumed. -/
theorem compactSpectrum_doubleLog_conductor_upper_floor :
    ∀ c : ℝ, compactProjectionDefect < c → ∀ᶠ n in atTop,
      moment Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) doubleLog /
        compactSpectrumConductorLogScale n < c := by
  have hupper : Tendsto (fun n =>
      (doubleLog (compactSpectrumConductorCap n) / compactSpectrumConductorLogScale n) *
        correction Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) +
      compactSpectrumDoubleLogRemainder n / compactSpectrumConductorLogScale n)
      atTop (𝓝 compactProjectionDefect) := by
    simpa only [one_mul, add_zero] using
      (compactSpectrum_cap_doubleLog_scale_ratio_tendsto_one.mul
        compactSpectrum_correction_tendsto_defect).add
      (compactSpectrumDoubleLogRemainder_tendsto_zero.div_atTop
        compactSpectrumConductorLogScale_tendsto_atTop)
  intro c hc
  filter_upwards [hupper.eventually_lt_const hc] with n hn
  have h := div_le_div_of_nonneg_right
    (doubleLog_moment_le_cap_correction_add_remainder Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n) (compactSpectrumConductorCap n)
      (fun i _ => compactSpectrumWeight_nonneg n i)
      (fun i _ => compactSpectrumEigenvalue_nonneg n i)
      (fun i _ => compactSpectrumEigenvalue_le_conductor_cap n i))
    (compactSpectrumConductorLogScale_pos n).le
  have hid (u v p d : ℝ) : (u * v + p) / d = (u / d) * v + p / d := by ring
  rw [hid] at h
  exact h.trans_lt hn

end RiemannResearch.RH.Pareto.CoefficientStabilization
