import RiemannResearch.Analysis.MontgomeryFejerRampPrecision

/-! # An adaptive Fejér bandwidth criterion for global RH and simplicity

At one finite height the sine-model ramp tends to zero as the bandwidth
tends to infinity, and the actual Fejér energy recovers the forward atom.
Varying the bandwidth with height gives an exact existence criterion. The
forward construction uses the collision-free conclusion; it supplies no
arithmetic choice of bandwidth independently of that conclusion. -/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open MontgomeryPositiveGap ActualZeroOrdinate ActualZeroCollisionCertificate

/-- The fixed-height limit measures the entire integer excess above the
diagonal, counted in ordered pairs. -/
theorem fejerSineRampDiscrepancy_fixed_height {T : ℝ} (hT : 1 < T) :
    Tendsto (fun R => fejerSineRampDiscrepancy T R) atTop
      (𝓝 ((actualCollision T : ℝ) - (Ncount 0 T : ℝ))) := by
  have hratio : Tendsto (fun R : ℝ => unfoldedCutoff T / R^2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_div_atTop _
  have h := ((fejer_limit_at_fixed_height hT).sub_const (Ncount 0 T : ℝ)).sub
    (hratio.div_const 3)
  rw [zero_div, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  rw [fejerSineRampDiscrepancy, fejer_model_value hR]
  change unfoldedCutoff T * fejerFormFactor T R - (Ncount 0 T : ℝ) - unfoldedCutoff T / R^2 / 3 = _
  ring

/-- A freely chosen bandwidth can make both the signed absolute error and
the finite-window bias vanish exactly when all nontrivial zeros are simple
and critical. The lower bandwidth schedule B is arbitrary. -/
theorem global_iff_exists_fejerSineRamp_schedule (B : ℝ → ℝ) :
    (RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1) ↔
    ∃ R : ℝ → ℝ, (∀ T, max 1 (B T) ≤ R T) ∧
      Tendsto (fun T => fejerSineRampDiscrepancy T (R T)) atTop (𝓝 0) ∧
      Tendsto (fun T => unfoldedCutoff T / (R T)^2) atTop (𝓝 0) := by
  constructor
  · intro hg
    have hex (T : ℝ) : ∃ r : ℝ, max 1 (B T) ≤ r ∧ (1 < T →
        |fejerSineRampDiscrepancy T r| < 1/T ∧ |unfoldedCutoff T / r^2| < 1/T) := by
      by_cases hT : 1 < T
      · have he := (actualCollision_eq_count_iff T).mpr
          (all_cutoffs_critical_simple_iff_global.mpr hg T)
        have hz := fejerSineRampDiscrepancy_fixed_height hT
        rw [he, sub_self] at hz
        have hb : Tendsto (fun r : ℝ => unfoldedCutoff T / r^2) atTop (𝓝 0) :=
          (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_div_atTop _
        have htol : 0 < 1/T := one_div_pos.mpr (zero_lt_one.trans hT)
        obtain ⟨r,hr,h₁,h₂⟩ := ((eventually_ge_atTop (max 1 (B T))).and
          ((Metric.tendsto_nhds.mp hz _ htol).and (Metric.tendsto_nhds.mp hb _ htol))).exists
        exact ⟨r,hr,fun _ => by simpa only [Real.dist_eq, sub_zero] using And.intro h₁ h₂⟩
      · exact ⟨max 1 (B T), le_rfl, fun h => (hT h).elim⟩
    choose R hR using hex
    have hsmall {f : ℝ → ℝ} (hf : ∀ T, 1 < T → |f T| < 1/T) :
        Tendsto f atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hinv : Tendsto (fun T : ℝ => 1/T) atTop (𝓝 0) := by
        simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
      filter_upwards [eventually_gt_atTop (1 : ℝ), hinv.eventually_lt_const hε] with T hT hεT
      simpa only [Real.dist_eq, sub_zero] using (hf T hT).trans hεT
    exact ⟨R, fun T => (hR T).1, hsmall (fun T hT => ((hR T).2 hT).1),
      hsmall (fun T hT => ((hR T).2 hT).2)⟩
  · rintro ⟨R,hR,he,hκ⟩
    exact global_of_fejerSineRamp_limits
      (Eventually.of_forall fun T => (le_max_left 1 (B T)).trans (hR T)) he hκ (by norm_num)

end RiemannResearch.Analysis.MontgomeryFormFactor
