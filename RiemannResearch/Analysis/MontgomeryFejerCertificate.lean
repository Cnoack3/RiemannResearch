/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFejerDensity
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroAnalyticDiagonal
import RiemannResearch.Analysis.OrdinateCollisionRemainder
import RiemannResearch.RH.RealZetaNonvanishing
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs

/-!
# Finite Fejér certificates for actual zeta zeros

Section 4 of the user-provided note `Montgomery_Pair_Correlation_Without_RH.md`
uses the fixed-height limit of the Fourier triangle to give two finite
certificates for criticality. The analytic diagonal allows multiple zeros.
The threshold is the contribution of one ordered pair in both directions.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology ComplexConjugate

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPoisson

private theorem sincSquared_tendsto_zero {v : ℝ} (hv : v ≠ 0) :
    Tendsto (fun R : ℝ => sincSquared R v) atTop (𝓝 0) := by
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hb : Tendsto (fun R : ℝ => (4 / v ^ 2) * (R⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (hi.pow 2).const_mul (4 / v ^ 2)
  apply squeeze_zero' (Eventually.of_forall fun R => sincSquared_nonneg R v) ?_ hb
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  calc
    _ ≤ 4 / (R ^ 2 * v ^ 2) := sincSquared_le_inverse_square hR.ne' hv
    _ = _ := by field_simp [hR.ne', hv]

private theorem fejer_pair_limit {L : ℝ} (hL : L ≠ 0) (d : ℝ) :
    Tendsto (fun R : ℝ => cauchyWeight d * sincSquared R (L * d))
      atTop (𝓝 (if d = 0 then (1 : ℝ) else 0)) := by
  by_cases h : d = 0
  · subst d
    simp [cauchyWeight]
  · simpa only [if_neg h, mul_zero] using
      (sincSquared_tendsto_zero (mul_ne_zero hL h)).const_mul (cauchyWeight d)

theorem fejer_limit_at_fixed_height {T : ℝ} (hT : 1 < T) :
    Tendsto (fun R : ℝ => (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R)
      atTop (𝓝 (actualCollision T : ℝ)) := by
  classical
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  let t := copyOrdinate T
  have hlim : Tendsto (fun R : ℝ => kernelEnergy t
        (fun d => cauchyWeight d * sincSquared R (Real.log T * d)))
      atTop (𝓝 (actualCollision T : ℝ)) := by
    unfold kernelEnergy actualCollision occurrenceCollision
    push_cast
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    simpa [t, sub_eq_zero] using fejer_pair_limit (Real.log_pos hT).ne' (t i - t j)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [fejerFormFactor_eq_kernelEnergy T hR]
  change _ = D * (_ / D)
  field_simp [hD.ne']
  rfl

theorem fejer_finite_certificate_iff {T : ℝ} (hT : 1 < T) :
    (∃ R : ℝ, 0 < R ∧ (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R <
      (Ncount 0 T : ℝ) + 2) ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  constructor
  · rintro ⟨R, hR, hsmall⟩
    have hD : 0 < T * Real.log T / (2 * Real.pi) :=
      div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
    have hle := (div_le_iff₀ hD).mp (collision_div_main_le_fejerFormFactor hT hR)
    have hlt : (actualCollision T : ℝ) < (Ncount 0 T : ℝ) + 2 :=
      (hle.trans_eq (mul_comm _ _)).trans_lt hsmall
    have hnat : actualCollision T < Ncount 0 T + 2 := by exact_mod_cast hlt
    have hn := actualCollision_eq_count_add_excess T
    obtain ⟨k, hk⟩ := actualCollision_sub_count_even T
    apply (actualCollision_eq_count_iff T).mp
    omega
  · intro hall
    have hl := fejer_limit_at_fixed_height hT
    rw [(actualCollision_eq_count_iff T).mpr hall] at hl
    have h2 : (Ncount 0 T : ℝ) < (Ncount 0 T : ℝ) + 2 := by linarith
    exact ((eventually_gt_atTop (0 : ℝ)).and (hl.eventually (gt_mem_nhds h2))).exists

theorem fejer_critical_line_iff {T : ℝ} (hT : 1 < T) :
    (∃ R : ℝ, 0 < R ∧ (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R <
      (analyticPairCount T : ℝ) + 2) ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  constructor
  · rintro ⟨R, hR, hs⟩ ρ hρ
    have hD : 0 < T * Real.log T / (2 * Real.pi) :=
      div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
    have hu := (div_le_iff₀ hD).mp (collision_div_main_le_fejerFormFactor hT hR)
    have hlt : (actualCollision T : ℝ) < (analyticPairCount T : ℝ) + 2 :=
      (hu.trans_eq (mul_comm _ _)).trans_lt hs
    have hnat : actualCollision T < analyticPairCount T + 2 := by exact_mod_cast hlt
    have hid := collision_eq_analytic_add_distinctZeroCollision T
    by_contra hoff
    have hbad := two_le_distinctZeroCollision_of_off_line hρ hoff
    omega
  · intro hall
    have heq := (collision_eq_analyticPairCount_iff T).mpr hall
    have hl := fejer_limit_at_fixed_height hT
    rw [heq] at hl
    have h2 : (analyticPairCount T : ℝ) < (analyticPairCount T : ℝ) + 2 := by linarith
    exact ((eventually_gt_atTop (0 : ℝ)).and (hl.eventually (gt_mem_nhds h2))).exists

theorem offCount_le_fejer_sub_analytic {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    (offCount T : ℝ) ≤ (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R -
      (analyticPairCount T : ℝ) := by
  have hD : 0 < T * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hf := (div_le_iff₀ hD).mp (collision_div_main_le_fejerFormFactor hT hR)
  have hc : (offCount T : ℝ) + (analyticPairCount T : ℝ) ≤ actualCollision T := by
    exact_mod_cast off_count_add_analytic_le_collision T
  linarith [mul_comm (fejerFormFactor T R) (T * Real.log T / (2 * Real.pi))]

theorem cofinal_fejer_critical_line_iff :
    (∀ H : ℝ, ∃ T R : ℝ, H ≤ T ∧ 1 < T ∧ 0 < R ∧
      (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R < (analyticPairCount T : ℝ) + 2) ↔
      ∀ H : ℝ, ∀ ρ ∈ cutoff H, ρ.re = 1 / 2 := by
  constructor
  · intro h H ρ hρ
    obtain ⟨T, R, hHT, hT, hR, hs⟩ := h H
    obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
    exact (fejer_critical_line_iff hT).mp ⟨R, hR, hs⟩ ρ
      (mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩)
  · intro h H
    let T := max H 2
    have hT : 1 < T := lt_of_lt_of_le (by norm_num) (le_max_right H 2)
    obtain ⟨R, hR, hs⟩ := (fejer_critical_line_iff hT).mpr (h T)
    exact ⟨T, R, le_max_left H 2, hT, hR, hs⟩

/-- The cofinal multiplicity-adjusted Fejér certificate is equivalent to RH. -/
theorem cofinal_fejer_critical_line_iff_RH :
    (∀ H : ℝ, ∃ T R : ℝ, H ≤ T ∧ 1 < T ∧ 0 < R ∧
      (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R < (analyticPairCount T : ℝ) + 2) ↔
      RiemannHypothesis := by
  rw [cofinal_fejer_critical_line_iff, RH.riemannHypothesis_iff_strip_zeros_on_line]
  constructor
  · intro hall s hz h0 h1
    have hne : s.im ≠ 0 := by
      intro hi
      have hs : (s.re : ℂ) = s := Complex.ext (by simp) (by simp [hi])
      exact (RH.riemannZeta_ofReal_ne_zero s.re h0 h1.ne) (by rwa [hs])
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hs : IsNontrivialZero s := ⟨hz, h0, h1⟩
      have hc : IsNontrivialZero (starRingEnd ℂ s) := by
        refine ⟨?_, by simpa only [Complex.conj_re] using h0,
          by simpa only [Complex.conj_re] using h1⟩
        rw [riemannZeta_conj hs.not_trivial.2, hz, map_zero]
      have hci : 0 < (starRingEnd ℂ s).im := by simpa using neg_pos.mpr hneg
      simpa only [Complex.conj_re] using hall _ _ (mem_cutoff.mpr ⟨hc, hci, le_rfl⟩)
    · exact hall s.im s (mem_cutoff.mpr ⟨⟨hz, h0, h1⟩, hpos, le_rfl⟩)
  · intro hall T s hs
    obtain ⟨⟨hz, h0, h1⟩, _, _⟩ := mem_cutoff.mp hs
    exact hall s hz h0 h1

/-- The finite Cauchy-weighted Fejér contribution of pairs at different heights. -/
def fejerNonzeroGapRemainder (T R : ℝ) : ℝ := by
  classical
  exact ∑ i : Copies T, ∑ j : Copies T, if copyOrdinate T i = copyOrdinate T j then 0 else
    cauchyWeight (copyOrdinate T i - copyOrdinate T j) *
      sincSquared R (Real.log T * (copyOrdinate T i - copyOrdinate T j))

theorem fejerNonzeroGapRemainder_nonneg (T R : ℝ) : 0 ≤ fejerNonzeroGapRemainder T R := by
  classical
  unfold fejerNonzeroGapRemainder
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by unfold cauchyWeight; positivity) (sincSquared_nonneg _ _)

theorem normalized_fejer_eq_collision_add_nonzeroGap {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R =
      (actualCollision T : ℝ) + fejerNonzeroGapRemainder T R := by
  classical
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  rw [fejerFormFactor_eq_kernelEnergy T hR]
  change D * (_ / D) = _
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hD.ne']
  unfold kernelEnergy actualCollision occurrenceCollision fejerNonzeroGapRemainder
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : copyOrdinate T i = copyOrdinate T j
  · simp [hij, cauchyWeight]
  · simp [hij]

/-- Subtracting the analytic diagonal leaves the exact same-height cross count
and the nonnegative different-height contribution. -/
theorem normalized_fejer_sub_analytic_eq {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R - (analyticPairCount T : ℝ) =
      (distinctZeroCollision T : ℝ) + fejerNonzeroGapRemainder T R := by
  rw [normalized_fejer_eq_collision_add_nonzeroGap hT hR,
    collision_eq_analytic_add_distinctZeroCollision]
  push_cast
  linarith

/-- A single off-line zero gives a two-pair obstruction at every larger cutoff,
uniformly over all positive Fejér radii. -/
theorem eventually_two_le_normalized_fejer_sub_analytic_of_off_line {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) (hi : 0 < ρ.im) (hoff : ρ.re ≠ 1 / 2) :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 < R →
      2 ≤ (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R -
        (analyticPairCount T : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop ρ.im] with T hT hheight
  intro R hR
  have htwo : (2 : ℝ) ≤ distinctZeroCollision T := by
    exact_mod_cast two_le_distinctZeroCollision_of_off_line
      (mem_cutoff.mpr ⟨hρ, hi, hheight⟩) hoff
  rw [normalized_fejer_sub_analytic_eq hT hR]
  linarith only [htwo, fejerNonzeroGapRemainder_nonneg T R]

/-- Finite bound for the proportion of zero occurrences that fail joint
simplicity and criticality. The denominator is the actual zero count. -/
theorem exceptional_proportion_le_normalized_fejer_excess {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) :
    ((Ncount 0 T : ℝ) - simpleCriticalCount T) / (Ncount 0 T : ℝ) ≤
      ((T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R - (Ncount 0 T : ℝ)) /
        (Ncount 0 T : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hcount : 2 * (Ncount 0 T : ℝ) ≤ (simpleCriticalCount T : ℝ) + actualCollision T := by
    exact_mod_cast twice_count_le_simpleCriticalCount_add_collision T
  rw [normalized_fejer_eq_collision_add_nonzeroGap hT hR]
  linarith only [hcount, fejerNonzeroGapRemainder_nonneg T R]

end RiemannResearch.Analysis.MontgomeryFormFactor
