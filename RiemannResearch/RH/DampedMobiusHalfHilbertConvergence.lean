/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorTruncationBounds
import RiemannResearch.RH.ParetoDominatedConvergence
import RiemannResearch.RH.DampedMobiusJointHeadLimits

/-!
# Full natural-order Hilbert convergence at half damping

The entire Hilbert cutoffs converge at epsilon = 1/2, including their
infinite physical tails. A single logarithmic envelope, proved by applying
the hyperbola estimate to truncated signed weights, discharges the missing
domination premise. The earlier absolute-convergence argument handles
epsilon > 1/2. Consequences include the full signed Gram limit, signed
bounds uniform in both cutoffs, and joint head limits at arbitrary rates.

Source for the underlying endpoint membership statement: J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and
a theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166. The proof here uses the repository's
PNT, signed Abel bounds, and exact hyperbola identities; the truncation
and domination argument is given explicitly, without a novelty claim.

Natural-order convergence does not assert summability over arbitrary
finite subsets of conductor indices, or absolute off-diagonal summability.
Subhalf arithmetic energy remains open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- A single summable endpoint envelope controls every full Hilbert cutoff,
including the physical coordinates beyond its conductor cutoff. -/
theorem dampedMobius_half_partial_uniform_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M n : ℕ, 0 < n → 200 ≤ Real.log (n : ℝ) →
      |hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n| ≤
        K * Real.sqrt (n : ℝ) / (6 + Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by
  obtain ⟨B, hB, hP⟩ := dampedMobius_half_prefix_log_bound
  obtain ⟨D, hD, hT⟩ := dampedMobius_half_density_tail_log_bound
  have hT' (t : ℕ) (ht : 0 < t) :
      |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
        positiveArithmeticPrefix (fun d => dampedMobiusWeight (1 / 2) d / (d : ℝ)) t| ≤
        D / (Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ)) := by
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hL := shiftedLog_pos ht1
    have h := hT t ht
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
      Real.rpow_neg ht0.le, Real.rpow_neg hL.le, ← Real.sqrt_eq_rpow] at h
    simpa only [positiveArithmeticPrefix, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm] using h
  refine ⟨2 + 24 * B + 16 * D, by positivity, ?_⟩
  intro M n hn hl
  have h := arithmeticFloorHilbertPartial_uniform_log_bound (dampedMobiusWeight (1 / 2))
    (dampedMobiusWeight_zero _) _ (W := 1) (by norm_num) hB hD
    dampedMobius_half_weight_bound hP hT' M n hn hl
  simpa only [mul_one] using h

/-- The naturally ordered full Hilbert cutoffs converge unconditionally at
the half-damping endpoint. The canonical arithmetic coordinates identify
the limit; no uniform-energy or tail premise is assumed. -/
theorem dampedMobius_half_cutoffs_converge :
    ∃ f : ThresholdHilbert,
      (∀ n : ℕ, hilbertSequence f n = dampedMobiusPrefix (1 / 2) n -
        (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)))
        atTop (𝓝 f) := by
  let g := fun n => dampedMobiusPrefix (1 / 2) n -
    (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re
  have hs : Summable (fun n => positiveWeight n * (g n) ^ 2) :=
    centered_dampedMobius_square_summable_of_half_le le_rfl
  let f := sequenceHilbert g hs
  have hcoord (n : ℕ) : hilbertSequence f n = g n := by
    exact congrFun (hilbertSequence_sequenceHilbert g hs
      (by simp [g, dampedMobiusPrefix, arithmeticFloorPrefix])) n
  refine ⟨f, hcoord, ?_⟩
  obtain ⟨K, hK, hbound⟩ := dampedMobius_half_partial_uniform_log_bound
  let A := fun n : ℕ => K * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-(3 / 4 : ℝ))
  have hA : Summable (fun n => positiveWeight n * (A n) ^ 2) := by
    apply square_summable_of_eventual_sqrt_shifted_log_bound hK
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hL := shiftedLog_pos (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    dsimp [A]
    rw [abs_of_nonneg (by positivity)]
  apply pareto_tendsto_of_eventual_dominated_coordinates _ f A hA
  · intro n
    rw [hcoord]
    exact dampedMobius_partial_coordinate_tendsto (by norm_num) n
  · have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually (eventually_ge_atTop (200 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with n hn hn1
    intro M
    dsimp [A]
    rw [Real.rpow_neg (by linarith : 0 ≤ 6 + Real.log (n : ℝ)), ← div_eq_mul_inv]
    exact hbound M n (by omega) hn

/-- Natural-order norm convergence with the forced arithmetic coordinates
throughout the full unconditional half-damping range. -/
theorem dampedMobius_cutoffs_converge_of_half_le {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ f : ThresholdHilbert,
      (∀ n : ℕ, hilbertSequence f n = dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  rcases eq_or_lt_of_le hε with heq | hlt
  · subst ε
    exact dampedMobius_half_cutoffs_converge
  · have hw := dampedMobius_half_weight_summable hlt
    have hc := (centered_dampedMobius_square_summable_iff hlt _).mp
      (centered_dampedMobius_square_summable_of_half_lt hlt)
    refine ⟨arithmeticFloorHilbert (dampedMobiusWeight ε), ?_, ?_⟩
    · intro n
      simpa only [dampedMobiusPrefix, hc] using
        arithmeticFloorHilbert_sequence (dampedMobiusWeight ε) hw n
    · exact ((arithmeticResidueTerm_summable
        (dampedMobiusWeight ε) hw).hasSum.tendsto_sum_nat).neg

/-- The complete signed Gram off-diagonal has the exact arithmetic limit
throughout epsilon >= 1 / 2, including the natural-order endpoint. -/
theorem dampedMobius_full_offDiagonal_tendsto_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Tendsto (dampedMobiusGramOffDiagonal ε) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) - dampedMobiusExactDiagonal ε)) := by
  obtain ⟨f, hcoord, hf⟩ := dampedMobius_cutoffs_converge_of_half_le hε
  have hpos : 0 < ε := by linarith
  have hd : Tendsto (dampedMobiusGramDiagonal ε) atTop
      (𝓝 (dampedMobiusExactDiagonal ε)) :=
    (dampedMobiusResidue_norm_sq_summable hpos).hasSum.tendsto_sum_nat
  have ht := (hf.norm.pow 2).sub hd
  have he : ‖f‖ ^ 2 = ∑' n : ℕ, positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2 := by
    rw [hilbert_norm_weighted_sq]
    simp only [hcoord]
  rw [he] at ht
  convert ht using 1
  funext M
  rw [dampedMobius_partial_norm_sq_eq_signed]
  ring

/-- There is no relative-rate restriction on the two diverging cutoffs
once full Hilbert convergence is available. -/
theorem dampedMobius_offDiagonal_unrestricted_joint_tendsto
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) (H M : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => dampedMobiusHeadOffDiagonal ε (H j) (M j)) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) - dampedMobiusExactDiagonal ε)) := by
  obtain ⟨f, hcoord, hf⟩ := dampedMobius_cutoffs_converge_of_half_le hε
  have hn : Tendsto (fun j =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M j) - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      (((hf.comp hM).sub_const f).norm.pow 2)
  apply dampedMobius_offDiagonal_joint_tendsto_of_head_error
    (by linarith) H M hH hM (centered_dampedMobius_square_summable_of_half_le hε)
  apply squeeze_zero _ _ hn
  · intro j
    exact Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
  · intro j
    have h := paretoHeadPairing_self_le (H j)
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M j) - f)
    simpa only [paretoHeadPairing, hilbertSequence_sub, Pi.sub_apply,
      hcoord, mul_assoc, ← pow_two] using h


/-- One finite constant bounds both the full Gram off-diagonal and every
finite signed head, independently of both cutoffs. -/
theorem dampedMobius_signed_bounds_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ B : ℝ, (∀ M : ℕ, dampedMobiusGramOffDiagonal ε M ≤ B) ∧
      ∀ H M : ℕ, dampedMobiusHeadOffDiagonal ε H M ≤ B := by
  obtain ⟨f, _, hf⟩ := dampedMobius_cutoffs_converge_of_half_le hε
  have h := hf.norm.pow 2
  rw [← Nat.cofinite_eq_atTop] at h
  obtain ⟨B, hB⟩ := h.bddAbove_range_of_cofinite
  have hb (M : ℕ) : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 ≤ B :=
    hB (Set.mem_range_self M)
  refine ⟨B, fun M => (dampedMobius_offDiagonal_le_partial_norm_sq ε M).trans (hb M), ?_⟩
  intro H M
  have hp := paretoHeadPairing_self_le H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  rw [dampedMobius_partial_head_eq_signed] at hp
  linarith [dampedMobiusHeadDiagonal_nonneg ε H M, hb M]

end RiemannResearch.RH.Pareto
