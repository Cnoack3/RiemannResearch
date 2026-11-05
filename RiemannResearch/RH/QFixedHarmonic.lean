/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QResolventHarmonicPrefix

/-!
# The fixed first resolvent step and a cofinal RH criterion

For the Q residual r, set b = Π B r and s = B r − b. The exact identity
⟪1,s⟫ = ⟪r,B r⟫ makes the mean of s faithful. A signed prime probe bounds
that mean in terms of the smaller of the two physical harmonic prefixes of b.
Since the first centered resolvent step is exactly (4/3) b, cofinal control of
that one fixed step suffices; approximating the full displacement is unnecessary.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFixedHarmonic
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSignedTailRigidity
open QShiftedReciprocal QAnnihilatorTailEscape QSquarefreeDisplacementRigidity
open QSquarefreeSmoothedProjection QSquarefreeDisplacementResolvent
open RiemannResearch.Analysis RiemannResearch.Analysis.CofinalMoments

private theorem correction_eq_zero_of_residual_eq_zero (h : limitingResidual = 0) :
    correction = 0 := by simp [correction, h]

private theorem residual_eq_zero_of_screened_mean_zero (h : inner ℝ qOne screened = 0) :
    limitingResidual = 0 := B_faithful _ (screened_mean_eq_energy.symm.trans h)

abbrev correctionSide := harmonicSideOf correction

/-- The first absolute moment of the reciprocal-smoothed source. -/
def sourceMoment : ℝ :=
  ∑' n : ℕ, |signedCoefficient (B limitingResidual) n| * (n : ℝ)

theorem sourceMoment_nonneg : 0 ≤ sourceMoment :=
  tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))

/-- Exact conversion of the normalized charge prefix to the physical harmonic sum. -/
theorem correction_charge_prefix_eq (ε : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), max (ε * signedCoefficient correction n) 0 * (n : ℝ)) =
      correctionSide ε X / zetaTwo := by
  rw [correctionSide, harmonicSideOf, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hpos := positiveQWeight_nonneg n
  have hpart : max (ε * signedCoefficient correction n) 0 =
      positiveQWeight n * max (ε * qSequence correction n) 0 := by
    rw [signedCoefficient, mul_left_comm ε (positiveQWeight n)]
    rcases le_total 0 (ε * qSequence correction n) with h | h
    · rw [max_eq_left h, max_eq_left (mul_nonneg hpos h)]
    · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hpos h), mul_zero]
  rw [hpart]
  by_cases h : n = 0
  · simp [h]
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    unfold positiveQWeight
    field_simp [hn, zetaTwo_pos.ne']

/-- The sign may be selected separately at every cutoff. -/
theorem screened_prefix_le (ε : ℝ) (hε : |ε| = 1) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), max ((-ε) * signedCoefficient screened n) 0 * (n : ℝ)) ≤ sourceMoment + correctionSide ε X / zetaTwo := by
  have hfirst : Summable (fun n : ℕ => |signedCoefficient (B limitingResidual) n| * (n : ℝ)) := by
    apply (signedCoefficient_B_firstMoment limitingResidual).abs.congr
    intro n
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), mul_comm]
  have hpoint (n : ℕ) : max ((-ε) * signedCoefficient screened n) 0 ≤
      |signedCoefficient (B limitingResidual) n| + max (ε * signedCoefficient correction n) 0 := by
    apply max_le
    · have hb := neg_le_abs (ε * signedCoefficient (B limitingResidual) n)
      rw [abs_mul, hε, one_mul] at hb
      rw [screened, signedCoefficient_sub]
      linarith [le_max_left (ε * signedCoefficient correction n) 0]
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _)
  calc
    _ ≤ ∑ n ∈ Finset.range (X + 1),
        (|signedCoefficient (B limitingResidual) n| * (n : ℝ) + max (ε * signedCoefficient correction n) 0 * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, correction_charge_prefix_eq]
      exact add_le_add (hfirst.sum_le_tsum _
        (fun n _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))) le_rfl

/-- At each cutoff the smaller of the positive and negative harmonic masses. -/
abbrev minimumCorrectionPrefix := minimumHarmonicPrefixOf correction

theorem correctionSide_mono (ε : ℝ) : Monotone (correctionSide ε) := by
  intro X Y h
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right h 1))
  intro n _ _
  exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)

theorem minimumCorrectionPrefix_mono : Monotone minimumCorrectionPrefix := by
  intro X Y h
  exact min_le_min (correctionSide_mono 1 h) (correctionSide_mono (-1) h)

theorem exists_best_correction_sign (X : ℕ) :
    ∃ ε : ℝ, |ε| = 1 ∧ correctionSide ε X = minimumCorrectionPrefix X := by
  rcases le_total (correctionSide 1 X) (correctionSide (-1) X) with h | h
  · exact ⟨1, abs_one, (min_eq_left h).symm⟩
  · exact ⟨-1, by norm_num, (min_eq_right h).symm⟩

/-- Vanishing of the faithful residual is equivalent to a polylogarithmic
bound for the smaller physical harmonic mass at arbitrarily large cutoffs. -/
theorem residual_zero_iff_cofinal_correction_polylog :
    limitingResidual = 0 ↔ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∃ᶠ X : ℕ in atTop, minimumCorrectionPrefix X ≤ C * (Real.log (X : ℝ)) ^ B := by
  constructor
  · intro hr
    refine ⟨0, 0, le_rfl, le_rfl, (Eventually.of_forall ?_).frequently⟩
    intro X
    simp [minimumCorrectionPrefix, minimumHarmonicPrefixOf, harmonicSideOf, correction_eq_zero_of_residual_eq_zero hr,
      show qSequence (0:QHilbert) = 0 from map_zero qSequenceLinear]
  · rintro ⟨B, C, hB, hC, hgood⟩
    apply residual_eq_zero_of_screened_mean_zero
    apply annihilator_mean_zero_of_cofinal_charge_polylog screened screened_mem_orthogonal
      sourceMoment minimumCorrectionPrefix _ sourceMoment_nonneg minimumCorrectionPrefix_mono B C hB hC hgood
    intro X
    obtain ⟨ε, hε, hs⟩ := exists_best_correction_sign X
    exact ⟨ε, hε, by simpa only [hs] using screened_prefix_le ε hε X⟩

/-- The exact finite first step of the centered iteration. -/
theorem firstStep_eq : resolventApprox 1 = (4/3 : ℝ) • correction := by
  simp [resolventApprox, centeredFeedback]

/-- Positive homogeneity holds at each signed cutoff, before selecting a sign. -/
theorem vectorSide_nonneg_smul (u : QHilbert) (c ε : ℝ) (hc : 0 ≤ c) (X : ℕ) :
    harmonicSideOf (c • u) ε X = c * harmonicSideOf u ε X := by
  unfold harmonicSideOf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he : qSequence (c • u) n = c * qSequence u n :=
    congrFun (map_smul qSequenceLinear c u) n
  rw [he, show ε * (c * qSequence u n) = c * (ε * qSequence u n) by ring]
  rcases le_total 0 (ε * qSequence u n) with h | h
  · rw [max_eq_left h, max_eq_left (mul_nonneg hc h)]
    ring
  · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc h)]
    simp

/-- Exact fixed-depth transfer; the factor is independent of the cutoff. -/
theorem firstStep_minimum_eq (X : ℕ) :
    minimumHarmonicPrefixOf (resolventApprox 1) X = (4/3 : ℝ) * minimumCorrectionPrefix X := by
  rw [firstStep_eq]
  change min (harmonicSideOf ((4/3 : ℝ) • correction) 1 X)
      (harmonicSideOf ((4/3 : ℝ) • correction) (-1) X) =
    (4/3 : ℝ) * min (correctionSide 1 X) (correctionSide (-1) X)
  rw [vectorSide_nonneg_smul _ _ _ (by norm_num), vectorSide_nonneg_smul _ _ _ (by norm_num)]
  rcases le_total (correctionSide 1 X) (correctionSide (-1) X) with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (4/3:ℝ)))]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (4/3:ℝ)))]

/-- No depth schedule: a cofinal polylog bound at depth one is equivalent to
vanishing of the Q residual for each fixed pair of nonnegative constants. -/
theorem residual_zero_iff_fixed_firstStep_cofinal_polylog (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    limitingResidual = 0 ↔ ∃ᶠ X : ℕ in atTop,
      minimumHarmonicPrefixOf (resolventApprox 1) X ≤ C * (Real.log (X : ℝ)) ^ B := by
  constructor
  · intro hr
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    have hm : minimumCorrectionPrefix X = 0 := by
      simp [minimumCorrectionPrefix, minimumHarmonicPrefixOf, harmonicSideOf, correction_eq_zero_of_residual_eq_zero hr,
        show qSequence (0:QHilbert) = 0 from map_zero qSequenceLinear]
    rw [firstStep_minimum_eq, hm, mul_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hlog _)
  · intro hg
    apply residual_zero_iff_cofinal_correction_polylog.mpr
    refine ⟨B, C, hB, hC, hg.mono ?_⟩
    intro X hX
    rw [firstStep_minimum_eq] at hX
    have hpos (ε : ℝ) : 0 ≤ correctionSide ε X :=
      Finset.sum_nonneg (fun n _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))
    have hm : 0 ≤ minimumCorrectionPrefix X := le_min (hpos 1) (hpos (-1))
    linarith

theorem rh_of_fixed_firstStep_cofinal_polylog (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefixOf (resolventApprox 1) X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis :=
  QMertensFirstMoment.rh_of_zero_projection_residual
    ((residual_zero_iff_fixed_firstStep_cofinal_polylog B C hB hC).mpr hg)

/-- Only the reverse implication invokes the explicit Báez-Duarte bridge. -/
theorem rh_iff_fixed_firstStep_cofinal_polylog
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    RiemannHypothesis ↔ ∃ᶠ X : ℕ in atTop,
      minimumHarmonicPrefixOf (resolventApprox 1) X ≤ C * (Real.log (X : ℝ)) ^ B :=
  ⟨fun hRH => (residual_zero_iff_fixed_firstStep_cofinal_polylog B C hB hC).mp
    (QMertensFirstMoment.residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH),
   rh_of_fixed_firstStep_cofinal_polylog B C hB hC⟩

end RiemannResearch.RH.QFixedHarmonic
