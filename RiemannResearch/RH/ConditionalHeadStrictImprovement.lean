import RiemannResearch.RH.ThreeGeneratorStrictImprovement

/-!
# Strict improvement of every finite legal exact head

Source: the existing three-generator detection argument for mean-zero witnesses;
the nonzero-mean branch below uses the exact periodic Cesaro defect formula.
All correlations use the full signed conditional energy. No lower bound uniform
in the head length or conductor is asserted.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.Cesaro

theorem cesaro_meanPulse_nonneg (d t : ℕ) (hd : 0 < d) :
    0 ≤ cesaro (meanPulse d) t := by
  unfold cesaro
  apply div_nonneg _ (Nat.cast_nonneg t)
  apply Finset.sum_nonneg
  intro n hn
  rw [meanPulse_eq_div_mod d n hd]
  positivity

/-- An explicit defect threshold makes the nonzero period mean detectable.
The sign is proved before summing the actual signed correlation. -/
theorem periodMean_mul_pulseCorrelation_pos
    (F : ℕ → ℝ) (Q d : ℕ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (hd : 0 < d)
    (B : ℝ)
    (hb : ∀ t, |periodDefect F Q t| ≤ B)
    (hm : periodMean F Q ≠ 0)
    (hlarge : B < |periodMean F Q| * (d : ℝ)) :
    0 < periodMean F Q * conditionalMeanInner F (meanPulse d) := by
  let m := periodMean F Q
  have hsign (t : ℕ) (ht : d ≤ t) : 0 < m * cesaro F t := by
    have htpos : 0 < t := hd.trans_le ht
    have htR : (0 : ℝ) < t := by exact_mod_cast htpos
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast ht
    have hsmall : B / (t : ℝ) < |m| := by
      apply (div_lt_iff₀ htR).mpr
      have hh := mul_le_mul_of_nonneg_left hdt (abs_nonneg m)
      dsimp [m] at *
      linarith
    have herr : |cesaro F t - m| < |m| := by
      rw [cesaro_from_defect F Q t htpos]
      have he : periodMean F Q + periodDefect F Q t / (t : ℝ) - m =
          periodDefect F Q t / (t : ℝ) := by dsimp [m]; ring
      rw [he, abs_div, abs_of_pos htR]
      exact (div_le_div_of_nonneg_right (hb t) htR.le).trans_lt hsmall
    have hm' : m ≠ 0 := hm
    rcases lt_or_gt_of_ne hm' with hmneg | hmpos
    · rw [abs_of_neg hmneg] at herr
      have hh := (abs_lt.mp herr).2
      exact mul_pos_of_neg_of_neg hmneg (by linarith)
    · rw [abs_of_pos hmpos] at herr
      have hh := (abs_lt.mp herr).1
      exact mul_pos hmpos (by linarith)
  have hs := (conditionalMeanInner_summable F (meanPulse d)
    hF (meanPulse_legal d hd)).mul_left m
  have hnonneg (k : ℕ) :
      0 ≤ m * (conditionalWeight k * cesaro F (k+1) * cesaro (meanPulse d) (k+1)) := by
    by_cases hk : k+1 < d
    · rw [cesaro_meanPulse_zero_before d (k+1) hk]
      simp
    · have hp := mul_nonneg
        (mul_nonneg (conditionalWeight_pos k).le (hsign (k+1) (by omega)).le)
        (cesaro_meanPulse_nonneg d (k+1) hd)
      nlinarith only [hp]
  have hpos :
      0 < m * (conditionalWeight (2*d-1) * cesaro F (2*d-1+1) *
        cesaro (meanPulse d) (2*d-1+1)) := by
    rw [show 2*d-1+1 = 1*(2*d) by omega,
      cesaro_meanPulse_complete_periods d 1 hd (by omega)]
    have hp := mul_pos (conditionalWeight_pos (2*d-1))
      (hsign (1*(2*d)) (by omega))
    nlinarith only [hp]
  have h := hs.tsum_pos hnonneg (2*d-1) hpos
  simpa only [tsum_mul_left, conditionalMeanInner, m] using h

/-- A nonzero period mean gives a late direction with nonzero actual correlation. -/
theorem exists_meanPulse_correlation_ne_zero_of_periodMean
    (F : ℕ → ℝ) (Q Y : ℕ) (hQ : 0 < Q)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hper : ∀ n, F (n+Q) = F n) (hm : periodMean F Q ≠ 0) :
    ∃ d : ℕ, Y < d ∧ conditionalMeanInner F (meanPulse d) ≠ 0 := by
  obtain ⟨B, _hB, hb⟩ := periodDefect_exists_bound F Q hQ hper
  have hmabs : 0 < |periodMean F Q| := abs_pos.mpr hm
  obtain ⟨d, hd⟩ := exists_nat_gt (max (Y : ℝ) (B / |periodMean F Q|))
  have hYd : Y < d := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hd)
  have hBd : B < |periodMean F Q| * (d : ℝ) := by
    have h := (div_lt_iff₀ hmabs).mp (lt_of_le_of_lt (le_max_right _ _) hd)
    nlinarith
  have hpos := periodMean_mul_pulseCorrelation_pos F Q d hF (by omega) B hb hm hBd
  refine ⟨d, hYd, ?_⟩
  intro he
  rw [he, mul_zero] at hpos
  exact lt_irrefl 0 hpos

end RiemannResearch.RH.CRTBlock

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.CRTBlock

/-- Every actual finite legal exact nonempty head admits a strict energy decrease.
The correction preserves the entire prescribed head, with no period-mean premise. -/
theorem exists_strict_conditionalHead_improvement
    (Y : ℕ) (hY : 0 < Y) (F : ℕ → ℝ) (hF : F ∈ conditionalHeadClass Y) :
    ∃ G ∈ conditionalHeadClass Y, conditionalMeanSquare G < conditionalMeanSquare F := by
  obtain ⟨Q, hQ, hperiod⟩ := legalSeedSpan_hasLegalReflectionPeriod
    (Set.Ici 1) (by intro a ha; exact ha) hF.1
  have hp := (hperiod Q (dvd_refl Q)).1
  by_cases hm : periodMean F Q = 0
  · have hz : F ∈ zeroMeanHeadClass Y := ⟨hF, Q, hQ, hp, hm⟩
    obtain ⟨d, hd, hclass, he, hlt⟩ := exists_threeGenerator_strict_improvement Y hY F hz
    exact ⟨_, hclass.1, hlt⟩
  · obtain ⟨d, hd, hi⟩ := exists_meanPulse_correlation_ne_zero_of_periodMean F Q Y hQ hF.1 hp hm
    have hdpos : 0 < d := by omega
    have hg := meanPulse_energy_pos d hdpos
    let u := -conditionalMeanInner F (meanPulse d) / conditionalMeanSquare (meanPulse d)
    refine ⟨fun n => F n + u*meanPulse d n,
      add_mul_mem_conditionalHeadClass Y F (meanPulse d) hF (meanPulse_legal d hdpos)
        (fun n _ hn => meanPulse_zero_before d n (by omega)) u, ?_⟩
    change conditionalMeanSquare
      (fun n => F n + (-conditionalMeanInner F (meanPulse d) /
        conditionalMeanSquare (meanPulse d))*meanPulse d n) < conditionalMeanSquare F
    rw [conditionalMeanSquare_optimal_scalar F (meanPulse d) hF.1
      (meanPulse_legal d hdpos) (ne_of_gt hg)]
    exact sub_lt_self _ (div_pos (sq_pos_of_ne_zero hi) hg)

/-- The unrestricted legal infimum is strictly below every actual finite witness. -/
theorem conditionalHeadMinimum_lt_energy
    (Y : ℕ) (hY : 0 < Y) (F : ℕ → ℝ) (hF : F ∈ conditionalHeadClass Y) :
    conditionalHeadMinimum Y < conditionalMeanSquare F := by
  obtain ⟨G, hG, hlt⟩ := exists_strict_conditionalHead_improvement Y hY F hF
  exact (conditionalHeadMinimum_le Y hG).trans_lt hlt

theorem conditionalHeadMinimum_not_mem_energies (Y : ℕ) (hY : 0 < Y) :
    conditionalHeadMinimum Y ∉ conditionalHeadEnergies Y := by
  rintro ⟨F, hF, he⟩
  have h := conditionalHeadMinimum_lt_energy Y hY F hF
  rw [he] at h
  exact lt_irrefl _ h

/-- Every head-preserving scalar gain is bounded by the actual variational
excess, including zero-energy directions. This keeps the full signed source. -/
theorem signed_gain_le_variational_excess
    (Y : ℕ) (F R : ℕ → ℝ) (hF : F ∈ conditionalHeadClass Y)
    (hR : R ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ n, 0 < n → n ≤ Y → R n = 0) :
    (conditionalMeanInner F R)^2 / conditionalMeanSquare R ≤
      conditionalMeanSquare F - conditionalHeadMinimum Y := by
  by_cases hr : conditionalMeanSquare R = 0
  · rw [hr, div_zero]
    exact sub_nonneg.mpr (conditionalHeadMinimum_le Y hF)
  · have h := conditionalHeadMinimum_le_signed_projection Y F R hF hR hzero hr
    linarith

/-- There can be no positive additive gain floor uniform over all finite
conductors: actual legal near-minimizers defeat every scalar direction at once. -/
theorem exists_head_with_all_signed_gains_small
    (Y : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ F ∈ conditionalHeadClass Y,
      ∀ R ∈ legalSeedSpan (Set.Ici 1),
        (∀ n, 0 < n → n ≤ Y → R n = 0) →
          (conditionalMeanInner F R)^2 / conditionalMeanSquare R < ε := by
  obtain ⟨F, hF, henergy⟩ := exists_head_energy_lt Y ε hε
  refine ⟨F, hF, ?_⟩
  intro R hR hzero
  have h := signed_gain_le_variational_excess Y F R hF hR hzero
  linarith

/-- All actual scalar gains vanish along a minimizing sequence, even for
directions chosen adaptively and with unbounded conductors. -/
theorem near_minimizer_signed_gains_tendsto_zero
    (Y : ℕ) (F R : ℕ → ℕ → ℝ)
    (hF : ∀ j, F j ∈ conditionalHeadClass Y)
    (hR : ∀ j, R j ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ j n, 0 < n → n ≤ Y → R j n = 0)
    (hlim : Filter.Tendsto (fun j => conditionalMeanSquare (F j))
      Filter.atTop (nhds (conditionalHeadMinimum Y))) :
    Filter.Tendsto
      (fun j => (conditionalMeanInner (F j) (R j))^2 / conditionalMeanSquare (R j))
      Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto
      (fun j => conditionalMeanSquare (F j) - conditionalHeadMinimum Y)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hlim.sub_const (conditionalHeadMinimum Y)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun j => div_nonneg (sq_nonneg _) (conditionalMeanSquare_nonneg _))
    (fun j => signed_gain_le_variational_excess Y (F j) (R j)
      (hF j) (hR j) (hzero j))

end RiemannResearch.RH.Pareto
