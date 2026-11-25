import RiemannResearch.Analysis.MontgomeryMovingPrimeProbeTrace

/-! # One-sided rational shell tests with cofinal signed prime-probe tests -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MontgomeryPositiveGap ActualZeroOrdinate DyadicZeroWasserstein Zeta23
open scoped Topology

/-- At each fixed positive width the signed trace equals the ordinary
positive-gap discrepancy up to a vanishing error, without assuming PCC. -/
theorem fixed_gap_error_sub_primeProbeTrace {r : ℝ} (hr : 0 < r) :
    Tendsto (fun T : ℝ => (positiveGapMass T r - sineGapMass r) -
      (sampledArgumentIncrement T r + primeProbeEnergy T r)) atTop (𝓝 0) := by
  have hD : Tendsto unfoldedCutoff atTop atTop :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).atTop_div_const (by positivity)
  have hs : Tendsto (fun T : ℝ => r / unfoldedCutoff T) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hD).const_mul r
  have hm : Tendsto (fun T : ℝ => sampledHeightIncrement countMain T r) atTop (𝓝 r) := by
    have h := (sampled_main_increment_div_width_tendsto (R := fun _ => r)
      (Eventually.of_forall fun _ => hr) hs).mul_const r
    simpa only [div_mul_cancel₀ _ hr.ne', one_mul] using h
  have ha : Tendsto (fun T : ℝ => sampledRvMError T r - sampledArgumentIncrement T r)
      atTop (𝓝 0) := by
    have h := (sampled_argument_comparison_tendsto (R := fun _ => r)
      (Eventually.of_forall fun _ => hr)).mul_const r
    simpa only [← sub_div, div_mul_cancel₀ _ hr.ne', zero_mul] using h
  have h := (hm.add ha).sub (primeProbeEnergy_tendsto hr.le)
  have hd := h.sub_const (sineGapMass r)
  rw [show r + 0 - (r - sineGapMass r) - sineGapMass r = 0 by ring] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [positiveGapMass_eq_sampled_main_add_RvMError hT hr]
  ring

/-- With the upper estimates on fixed rational shells, eventual one-sided
signed trace estimates at cofinally many fixed integer widths characterize
ordinary positive-gap PCC. The choice of integer precedes the height limit. -/
theorem positiveGapPCC_iff_shellUpper_and_cofinalPrimeProbeTrace :
    PositiveGapPCC ↔
      (∀ a b : ℚ, 0 ≤ a → a < b → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T : ℝ in atTop, positiveGapMass T b - positiveGapMass T a ≤
          sineGapMass b - sineGapMass a + ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ n : ℕ, m < n ∧
        ∀ᶠ T : ℝ in atTop,
          -ε ≤ sampledArgumentIncrement T n + primeProbeEnergy T n) := by
  constructor
  · intro h
    refine ⟨(positiveGapPCC_iff_rationalShellUpper_and_cofinalAffineLower.mp h).1, ?_⟩
    intro ε hε m
    refine ⟨m + 1, Nat.lt_succ_self _, ?_⟩
    have hs := positiveGapPCC_iff_primeProbeTrace.mp h ((m + 1 : ℕ) : ℚ) (by positivity)
    have hl := hs.eventually_const_lt (neg_lt_zero.mpr hε)
    simpa only [Rat.cast_natCast] using hl.mono (fun _ ht => ht.le)
  · rintro ⟨hshell, htrace⟩
    apply positiveGapPCC_iff_rationalShellUpper_and_cofinalAffineLower.mpr
    refine ⟨hshell, ?_⟩
    intro ε hε m
    obtain ⟨n, hmn, hn⟩ := htrace (ε / 2) (half_pos hε) m
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_le m).trans_lt hmn
    refine ⟨n, hmn, ?_⟩
    have he := (fixed_gap_error_sub_primeProbeTrace hn').eventually_const_lt
      (neg_lt_zero.mpr (half_pos hε))
    filter_upwards [he, hn] with T hgap hsign
    linarith only [hgap, hsign, sineGapMass_lower hn'.le]

#print axioms fixed_gap_error_sub_primeProbeTrace
#print axioms positiveGapPCC_iff_shellUpper_and_cofinalPrimeProbeTrace

end RiemannResearch.Analysis.MontgomeryPrimeTrace
