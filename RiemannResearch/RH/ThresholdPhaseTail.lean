import RiemannResearch.RH.ThresholdPhaseLowerBound

/-!
# A complete two-sided finite-head certificate for the phase constant

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, 8 September 2026,
Section 8, equation `eq:Stail`. The telescoping proof gives the stronger
lower correction `1 / (144 * (N+1)^3)`, and works even for `N=0`.
All summability and limit hypotheses are discharged for the actual summands.
-/

namespace RiemannResearch.RH.TwoSeedThreshold

open scoped BigOperators
open Filter

/-- Stronger than the stated paper bound: `N+1`, rather than `N`, appears
in the cubic denominator, so the zero-head case is also included. -/
theorem phaseTail_lower (N : ℕ) :
    1 / (12 * ((N : ℝ) + 1)) - 1 / (144 * ((N : ℝ) + 1)^3) ≤ phaseTail N := by
  have hnat : Tendsto (fun J : ℕ => J + N + 1) atTop atTop := by
    apply tendsto_atTop_mono (fun J => ?_) tendsto_id
    change J ≤ J + N + 1
    omega
  have hinv : Tendsto (fun J : ℕ => 1 / ((N : ℝ) + J + 1)) atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).comp hnat)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div,
      add_comm, add_left_comm, add_assoc] using h
  have hB : Tendsto (fun J : ℕ =>
      1 / (12 * ((N : ℝ) + J + 1)) -
        1 / (144 * ((N : ℝ) + J + 1)^3)) atTop (nhds 0) := by
    have h : Tendsto (fun J : ℕ =>
        (1 / ((N : ℝ) + J + 1)) / 12 -
          (1 / ((N : ℝ) + J + 1))^3 / 144) atTop (nhds 0) := by
      simpa using (hinv.div_const 12).sub ((hinv.pow 3).div_const 144)
    convert h using 1
    funext J
    have hx : 0 < (N : ℝ) + J + 1 := by positivity
    field_simp
    <;> ring
  have hlim : Tendsto (fun J : ℕ =>
      (1 / (12 * ((N : ℝ) + 1)) - 1 / (144 * ((N : ℝ) + 1)^3)) -
        (1 / (12 * ((N : ℝ) + J + 1)) -
          1 / (144 * ((N : ℝ) + J + 1)^3))) atTop
      (nhds (1 / (12 * ((N : ℝ) + 1)) - 1 / (144 * ((N : ℝ) + 1)^3))) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hB
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro J
  exact (phase_sum_lower_telescoping N J).trans
    ((phaseDelta_shift_summable N).sum_le_tsum _
      (fun k _ => le_of_lt (phaseDelta_pos (by omega))))

/-- The actual constant has a complete two-sided rational tail certificate. -/
theorem universalPhaseConstant_certificate (N : ℕ) :
    (∑ k ∈ Finset.range N, phaseDelta (k + 1)) +
        1 / (12 * ((N : ℝ) + 1)) - 1 / (144 * ((N : ℝ) + 1)^3) ≤
      universalPhaseConstant ∧
    universalPhaseConstant ≤ (∑ k ∈ Finset.range N, phaseDelta (k + 1)) +
      1 / (12 * ((N : ℝ) + 1)) := by
  have hl := phaseTail_lower N
  have hu := phaseTail_le_twelfth N
  rw [universalPhaseConstant_head_tail N]
  constructor <;> linarith

/-- A simple exact rational enclosure needing no decimal logarithm certificate. -/
theorem universalPhaseConstant_rational_bounds :
    (11 : ℝ) / 144 ≤ universalPhaseConstant ∧ universalPhaseConstant ≤ 1 / 12 := by
  constructor
  · have h := phaseTail_lower 0
    norm_num [phaseTail, universalPhaseConstant] at h ⊢
    exact h
  · exact universalPhaseConstant_le_twelfth

end RiemannResearch.RH.TwoSeedThreshold
