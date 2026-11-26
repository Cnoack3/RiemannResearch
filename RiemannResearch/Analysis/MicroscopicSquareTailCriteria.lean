import RiemannResearch.Analysis.MicroscopicCountTail
import RiemannResearch.Analysis.MicroscopicDistinctGapCriterion
import RiemannResearch.Analysis.MicroscopicPrimeVacancy
import RiemannResearch.Analysis.MicroscopicRankDeletion
import RiemannResearch.Analysis.MicroscopicRankTail
import RiemannResearch.Analysis.MontgomeryFiniteIndexGap

/-! Qualitative consequences of uniform integrability of translated squared zero counts.
The index and deletion arguments develop the truncation argument of
`RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md`. For each error tolerance only
one rank and a height threshold for that rank are required. -/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MicroscopicSquareTailCriteria
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open ZeroDPPCorrelation ZeroDPPCollisionLoss ZeroDPPRankVacancy ZeroDPPVacancyDensity
open MicroscopicRankCover MicroscopicPrimeVacancy MontgomeryPositiveGap
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- Asymptotic uniform integrability, stated for the actual cutoff counts. -/
def VanishingTranslatedSquareTail (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ᶠ T : ℝ in atTop,
    truncatedWindowSecondMoment T b J < ε

theorem vanishingTranslatedSquareTail_of_exponential {b : ℝ}
    (he : ExpTranslatedSquareTail b) : VanishingTranslatedSquareTail b := by
  obtain ⟨A, c, _, hc, h⟩ := he
  have hlim := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hc)).2
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim' : Tendsto (fun J : ℕ => A * Real.exp (-c * (J : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlim.const_mul A
  intro ε hε
  obtain ⟨J, hJ⟩ := (hlim'.eventually_lt_const hε).exists
  exact ⟨J, h.mono (fun T hT => (hT J).trans_lt hJ)⟩

theorem vanishingTranslatedSquareTail_of_third {b : ℝ}
    (h3 : BoundedTranslatedThirdMoment b) : VanishingTranslatedSquareTail b := by
  obtain ⟨C, _, hC⟩ := h3
  intro ε hε
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 0 (C / ε))
  have hj : (0 : ℝ) < J := (le_max_left _ _).trans_lt hJ
  have hsmall : C / (J : ℝ) < ε := (div_lt_iff₀ hj).2 (by
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hJ)
    simpa [mul_comm] using h)
  refine ⟨J, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with T hC'T hT
  let H := b / (Real.log T / (2 * Real.pi))
  let K := actualWindowCount T H
  have hi := truncatedSquare_integrable (copyOrdinate T) T H J
  have hu := (actual_cube_integrable T H).const_mul ((J : ℝ)⁻¹)
  have hle : (∫ t : ℝ, if (J : ℝ) < K t then (K t)^2 else 0) ≤
      ∫ t : ℝ, (J : ℝ)⁻¹ * (K t)^3 := by
    apply integral_mono hi hu
    intro t
    change (if (J : ℝ) < K t then (K t)^2 else 0) ≤ (J : ℝ)⁻¹ * (K t)^3
    by_cases ht : (J : ℝ) < K t
    · rw [if_pos ht, ← div_eq_inv_mul, le_div_iff₀ hj]
      nlinarith only [mul_le_mul_of_nonneg_left ht.le (sq_nonneg (K t))]
    · rw [if_neg ht]
      exact mul_nonneg (inv_nonneg.mpr hj.le) (pow_nonneg (actual_window_nonneg T H t) _)
  rw [integral_const_mul] at hle
  calc
    truncatedWindowSecondMoment T b J ≤ ((J : ℝ)⁻¹ * (∫ t : ℝ, (K t)^3)) / T :=
      div_le_div_of_nonneg_right hle hT.le
    _ = ((∫ t : ℝ, (K t)^3) / T) / (J : ℝ) := by ring
    _ ≤ C / (J : ℝ) := div_le_div_of_nonneg_right hC'T hj.le
    _ < ε := hsmall

private theorem truncatedWindowSecondMoment_antitone {T : ℝ} (hT : 0 ≤ T) (b : ℝ) :
    Antitone (truncatedWindowSecondMoment T b) := by
  let H := b / (Real.log T / (2 * Real.pi))
  let K := actualWindowCount T H
  intro i j hij
  apply div_le_div_of_nonneg_right _ hT
  apply integral_mono (truncatedSquare_integrable (copyOrdinate T) T H j)
    (truncatedSquare_integrable (copyOrdinate T) T H i)
  intro t
  change (if (j : ℝ) < K t then (K t)^2 else 0) ≤ (if (i : ℝ) < K t then (K t)^2 else 0)
  have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  by_cases hj : (j : ℝ) < K t
  · simp only [if_pos hj, if_pos (hcast.trans_lt hj), le_refl]
  · rw [if_neg hj]
    split_ifs <;> positivity

/-- Every diverging chronological rank recovers the full fixed-width mass.
There is no growth or monotonicity requirement on the cutoff. -/
theorem tendsto_movingRankError {q : ℝ} (hq : 0 < q)
    (htail : VanishingTranslatedSquareTail (2 * q))
    {J : ℝ → ℕ} (hJ : Tendsto J atTop atTop) :
    Tendsto (fun T => positiveGapMass T q - finiteIndexGapMass T q (J T)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := htail (ε*q) (mul_pos hε hq)
  filter_upwards [hj, eventually_rankTail_le_truncated hq, eventually_gt_atTop (1 : ℝ),
    hJ.eventually (eventually_ge_atTop j)] with T hsmall hr hT hjT
  rw [Real.dist_eq, sub_zero]
  calc
    |positiveGapMass T q - finiteIndexGapMass T q (J T)| ≤ actualRankTail T q (J T) :=
      positiveGapMass_sub_finiteIndexGapMass_le hT q (J T)
    _ ≤ truncatedWindowSecondMoment T (2 * q) (J T) / q := hr _
    _ ≤ truncatedWindowSecondMoment T (2 * q) j / q :=
      div_le_div_of_nonneg_right
        (truncatedWindowSecondMoment_antitone (zero_lt_one.trans hT).le _ hjT) hq.le
    _ < ε := (div_lt_iff₀ hq).2 hsmall

theorem positiveGapPCC_iff_finiteIndexGap_of_squareTail
    (htail : ∀ q : ℚ, 0 < q → VanishingTranslatedSquareTail (2*(q : ℝ))) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun J : ℕ => limsup
        (fun T : ℝ => |finiteIndexGapMass T q J - sineGapMass q|) atTop) atTop (𝓝 0) := by
  apply positiveGapPCC_iff_finiteIndexGap_limsup
  intro q hq ε hε
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨j, hj⟩ := htail q hq (ε*(q : ℝ)) (mul_pos hε hqr)
  filter_upwards [eventually_ge_atTop j] with J hJ
  filter_upwards [hj, eventually_rankTail_le_truncated hqr, eventually_gt_atTop (1 : ℝ)]
    with T hsmall hr hT
  exact (positiveGapMass_sub_finiteIndexGapMass_le hT q J).trans_lt
    ((hr J).trans_lt ((div_lt_iff₀ hqr).2
      ((truncatedWindowSecondMoment_antitone (zero_lt_one.trans hT).le _ hJ).trans_lt hsmall)))

theorem positiveGapPCC_iff_movingRank {J : ℚ → ℝ → ℕ}
    (hJ : ∀ q : ℚ, 0 < q → Tendsto (J q) atTop atTop)
    (htail : ∀ q : ℚ, 0 < q → VanishingTranslatedSquareTail (2*(q : ℝ))) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => finiteIndexGapMass T q (J q T)) atTop (𝓝 (sineGapMass q)) := by
  rw [positiveGapPCC_iff_rationalWidthLimits]
  constructor
  · intro h q hq
    have he := tendsto_movingRankError (by exact_mod_cast hq : (0 : ℝ) < q)
      (htail q hq) (hJ q hq)
    simpa only [sub_zero, sub_sub_cancel] using (h q hq).sub he
  · intro h q hq
    have he := tendsto_movingRankError (by exact_mod_cast hq : (0 : ℝ) < q)
      (htail q hq) (hJ q hq)
    simpa only [zero_add, sub_add_cancel] using he.add (h q hq)

/-- Deleting a vanishing fraction of chronological labels has vanishing
fixed-width pair cost. Equal-height pairs of distinct labels are included. -/
theorem tendsto_deletedPairCount_of_vanishingDensity {q : ℝ} (hq : 0 < q)
    (htail : VanishingTranslatedSquareTail (2 * q))
    {S : ℝ → Finset ℕ} (hS : ∀ᶠ T : ℝ in atTop, S T ⊆ Finset.range (Ncount 0 T))
    (hd : Tendsto (fun T => ((S T).card : ℝ) / normalizer T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => MicroscopicRankDeletion.deletedPairCount (Ncount 0 T) (S T)
      (cutoffOrdinate T) (q / (Real.log T / (2 * Real.pi))) / normalizer T) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨J, htailJ⟩ := htail ((ε/2)*q) (mul_pos (half_pos hε) hq)
  have hlim : Tendsto (fun T : ℝ => 2*(J : ℝ)*(((S T).card : ℝ) / normalizer T))
      atTop (𝓝 0) := by simpa using hd.const_mul (2*(J : ℝ))
  filter_upwards [hS, htailJ, eventually_rankTail_le_truncated hq, eventually_gt_atTop (1 : ℝ),
      hlim.eventually_lt_const (half_pos hε)] with T hsT hjT hr ht hsmall
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans ht) (Real.log_pos ht)) (by positivity)
  have hp : 0 ≤ MicroscopicRankDeletion.deletedPairCount (Ncount 0 T) (S T)
      (cutoffOrdinate T) (q / (Real.log T / (2 * Real.pi))) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    split_ifs <;> norm_num
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hp hD.le)]
  have hr' : actualRankTail T q J < ε/2 := (hr J).trans_lt ((div_lt_iff₀ hq).2 hjT)
  have h := MicroscopicRankDeletion.normalized_deletedPairCount_le ht q J (S T) hsT
  exact h.trans_lt ((add_lt_add hsmall hr').trans_eq (by ring))

private theorem primeDeletedFraction_nonneg {T : ℝ} (ht : 1 < T) :
    0 ≤ primeDeletedFraction T := by
  have hx : 0 ≤ (Ncount 0 T : ℝ) - (actualOrdinateSupport T).card := by
    rw [← logarithmic_cutoff_vacancy]
    exact Finset.sum_nonneg fun i _ =>
      sub_nonneg.mpr ((limitingLaw_isDPP _).diagonal_bounds (liftCopy T i)).2
  exact div_nonneg hx ((div_pos (mul_pos (zero_lt_one.trans ht) (Real.log_pos ht))
    (by positivity : 0 < 2 * Real.pi)).le)

private theorem eventually_primeMeanWindowVacancy_eq_deleted {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ T : ℝ in atTop, meanWindowVacancy primeFrequencies T b = b * primeDeletedFraction T := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_supported_width b] with T ht hf
  let L := Real.log T / (2 * Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos ht) (by positivity)
  rw [← primeVacancy_eq_deleted, meanWindowVacancy,
    integral_windowVacancy primeFrequencies T _ (div_nonneg hb hL.le) (hf b hb le_rfl).2]
  have hn : normalizer T = T*L := by dsimp [normalizer,L]; ring
  rw [hn]
  change _ * (b/L) / T = b * (_/(T*L))
  field_simp [hL.ne', (zero_lt_one.trans ht).ne']

/-- Loss on a single nondegenerate interval detects the normalized excess
of occurrences. The reverse implication uses only asymptotic uniform
integrability, and the forward implication uses only the finite lower bound. -/
theorem prime_triangleLoss_tendsto_iff_deleted {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (htail : VanishingTranslatedSquareTail b) :
    Tendsto (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0) ↔
      Tendsto primeDeletedFraction atTop (𝓝 0) := by
  have hw : 0 < b^2 - a^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hab) (add_pos_of_pos_of_nonneg (ha.trans_lt hab) ha)]
  constructor
  · intro hl
    have hu : Tendsto (fun T : ℝ => triangleLoss primeFrequencies T a b / (b^2-a^2))
        atTop (𝓝 0) := by simpa using hl.div_const (b^2-a^2)
    refine squeeze_zero_norm' ?_ hu
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T ht
    rw [Real.norm_eq_abs, abs_of_nonneg (primeDeletedFraction_nonneg ht), le_div_iff₀ hw,
      mul_comm]
    exact prime_triangleLoss_lower ht ha hab.le
  · intro hd
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let B := 2*(b-a)
    have hB : 0 < B := mul_pos (by norm_num) (sub_pos.mpr hab)
    have hx : 0 < ε/(2*B) := div_pos hε (by positivity)
    obtain ⟨J, htailJ⟩ := htail _ hx
    have hlim : Tendsto (fun T : ℝ => (J : ℝ)*(b*primeDeletedFraction T)) atTop (𝓝 0) := by
      simpa using (hd.const_mul b).const_mul (J : ℝ)
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      eventually_primeMeanWindowVacancy_eq_deleted (ha.trans hab.le),
      eventually_triangleBudget_split primeFrequencies ha hab.le, htailJ,
      hlim.eventually_lt_const hx] with T ht hmean hbudget htailT hsmall
    have ⟨h1,h2⟩ := triangleLoss_budget_sandwich primeFrequencies ht hab.le
    have hp : 0 ≤ triangleLoss primeFrequencies T a b := by linarith only [h1,h2]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hp]
    have hbound := (h1.trans (hbudget J))
    rw [hmean] at hbound
    change triangleLoss primeFrequencies T a b ≤ B * _ at hbound
    apply hbound.trans_lt
    calc
      B * ((J : ℝ) * (b * primeDeletedFraction T) + truncatedWindowSecondMoment T b J) <
          B * (ε / (2*B) + ε / (2*B)) :=
        mul_lt_mul_of_pos_left (add_lt_add hsmall htailT) hB
      _ = ε := by
        field_simp [hB.ne']
        ring

theorem prime_triangleLoss_all_intervals_iff_deleted
    (htail : ∀ b : ℝ, 0 < b → VanishingTranslatedSquareTail b) :
    (∀ a b : ℝ, 0 ≤ a → a < b →
      Tendsto (fun T : ℝ => triangleLoss primeFrequencies T a b) atTop (𝓝 0)) ↔
      Tendsto primeDeletedFraction atTop (𝓝 0) := by
  constructor
  · intro h
    exact (prime_triangleLoss_tendsto_iff_deleted (a := 0) (b := 1) le_rfl
      zero_lt_one (htail 1 zero_lt_one)).mp (h 0 1 le_rfl zero_lt_one)
  · intro h a b ha hab
    exact (prime_triangleLoss_tendsto_iff_deleted ha hab (htail b (ha.trans_lt hab))).mpr h

open DistinctOrdinatePCC MicroscopicPositiveGapProjection

theorem correction_tendsto_of_squareTail_and_simpleDensity {q : ℝ} (hq : 0 < q)
    (htail : VanishingTranslatedSquareTail (q+2))
    (hd : Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun T : ℝ => multiplicityCorrection T q) atTop (𝓝 0) := by
  have hv := (logarithmic_relativeVacancy_tendsto_zero_iff.mpr hd).mul tendsto_count_div_mainTerm
  rw [zero_mul] at hv
  have hdel : Tendsto primeDeletedFraction atTop (𝓝 0) := by
    apply hv.congr'
    filter_upwards [tendsto_count_div_mainTerm.eventually_const_lt (zero_lt_one : (0 : ℝ) < 1)]
      with T hT
    have hN : (Ncount 0 T : ℝ) ≠ 0 := by
      intro hn
      simp [hn] at hT
    change (cutoffVacancy _ T / (Ncount 0 T : ℝ)) *
      ((Ncount 0 T : ℝ) / normalizer T) = primeDeletedFraction T
    rw [primeDeletedFraction, logarithmic_cutoff_vacancy, ← mul_div_assoc, div_mul_cancel₀ _ hN]
  have hl := (prime_triangleLoss_tendsto_iff_deleted (by linarith : 0 ≤ q+1)
    (by linarith : q+1 < q+2) htail).mpr hdel
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T ht
    exact (correction_sandwich ht q).1
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T ht
    exact (correction_sandwich ht q).2

/-- The translated third moment in the distinct-ordinate transfer can be
replaced by uniform integrability of the translated square. -/
theorem positiveGapPCC_iff_distinctLaw_of_squareTail (hm : ShortWindowSecondMomentUpper)
    (htail : ∀ q : ℚ, 0 < q → VanishingTranslatedSquareTail ((q : ℝ)+2)) :
    PositiveGapPCC ↔ DistinctPositiveGapLaw := by
  constructor
  · intro hp q hq
    have hc := correction_tendsto_of_squareTail_and_simpleDensity
      (by exact_mod_cast hq : (0 : ℝ) < q) (htail q hq) (density_one_of_positiveGapPCC hp hm).1
    exact (actual_tendsto_iff_distinct_of_correction hc).mp
      (positiveGapPCC_iff_rationalWidthLimits.mp hp q hq)
  · intro hs
    have hd := density_one_of_rationalDistinctAffineLower (rationalDistinctAffineLower_of_law hs) hm
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    have hc := correction_tendsto_of_squareTail_and_simpleDensity
      (by exact_mod_cast hq : (0 : ℝ) < q) (htail q hq) hd
    exact (actual_tendsto_iff_distinct_of_correction hc).mpr (hs q hq)

end RiemannResearch.Analysis.MicroscopicSquareTailCriteria
