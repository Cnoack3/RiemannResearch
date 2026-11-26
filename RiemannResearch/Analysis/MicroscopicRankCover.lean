import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.ZeroDPPVacancyDensity

/-!
# Rank truncation for microscopic zero pairs

The construction counts chronologically ordered labels and permits equal ordinates.
A pair of span at most h is captured by windows of width 2h for a set of
translations of measure at least h. The analytic majorant is explicit.
See the repository's microscopic Selberg trace note (2026-11-25).
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.MicroscopicRankCover
open ActualZeroOrdinate ActualZeroWindowVariance OrdinateWindowVariance
open ZeroDPPCorrelation ZeroDPPCollisionLoss ZeroDPPVacancyDensity

/-- Each unordered pair appears once. Ties are labeled in chronological order. -/
def rankTailCount (n J : ℕ) (x : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if i + J < j ∧ x j - x i ≤ h then 1 else 0

def crowdedSquare (J : ℕ) (k : ℝ) : ℝ := if (J : ℝ) < k then k^2 else 0

def actualRankTail (T q : ℝ) (J : ℕ) : ℝ :=
  rankTailCount (Ncount 0 T) J (cutoffOrdinate T) (q / (Real.log T / (2 * Real.pi))) /
    normalizer T

private lemma wp_nonneg (T h x t : ℝ) : 0 ≤ windowPulse T h x t := by
  unfold windowPulse pulse Set.indicator
  split_ifs <;> norm_num

private lemma rank_forces_crowding {n J i j : ℕ} {x : ℕ → ℝ}
    (hmono : Monotone x) {T H t : ℝ}
    (hj : j < n) (hrank : i + J < j)
    (hiw : t ∈ Ioc (max 0 (x i - H)) (min T (x i)))
    (hjw : t ∈ Ioc (max 0 (x j - H)) (min T (x j))) :
    (J : ℝ) < windowCount (Finset.range n) x T H t := by
  classical
  let s := (Finset.range n).filter (fun k => t ∈ Ioc (max 0 (x k - H)) (min T (x k)))
  have hsub : Finset.Icc i j ⊆ s := by
    intro k hk
    obtain ⟨hik,hkj⟩ := Finset.mem_Icc.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt hkj hj), ?_⟩
    simp only [Set.mem_Ioc, max_lt_iff, le_min_iff] at hiw hjw ⊢
    exact ⟨⟨hiw.1.1, lt_of_le_of_lt (sub_le_sub_right (hmono hkj) H) hjw.1.2⟩,
      ⟨hiw.2.1, hiw.2.2.trans (hmono hik)⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hn : J < s.card := by omega
  have he : windowCount (Finset.range n) x T H t = (s.card : ℝ) := by
    simp [s, windowCount, windowPulse, pulse, Set.indicator, Finset.sum_boole]
  rw [he]
  exact_mod_cast hn

/-- Finite covering inequality for any integrable pointwise majorant of the
crowded-window squared count. A lower ordinate floor removes the left clip. -/
theorem rankTailCount_cover {n J : ℕ} {x : ℕ → ℝ} {T h : ℝ}
    (hmono : Monotone x) (hx : ∀ i < n, 2*h ≤ x i ∧ x i ≤ T)
    {g : ℝ → ℝ} (hg : Integrable g)
    (hdom : ∀ t, crowdedSquare J (windowCount (Finset.range n) x T (2*h) t) ≤ g t) :
    h * rankTailCount n J x h ≤ ∫ t : ℝ, g t := by
  classical
  let term (i j : ℕ) (t : ℝ) := if i + J < j ∧ x j - x i ≤ h then
    windowPulse T (2*h) (x i) t * windowPulse T (2*h) (x j) t else 0
  have hterm (i j : ℕ) : Integrable (term i j) := by
    by_cases hc : i + J < j ∧ x j - x i ≤ h
    · simpa only [term, if_pos hc] using windowPulse_mul_integrable T (2*h) (x i) (x j)
    · simp only [term, if_neg hc]
      simp
  have hmass (i j : ℕ) (hi : i < n) (hj : j < n) :
      h * (if i + J < j ∧ x j - x i ≤ h then (1 : ℝ) else 0) ≤ ∫ t, term i j t := by
    by_cases hc : i + J < j ∧ x j - x i ≤ h
    · simp only [term, if_pos hc, mul_one]
      simp_rw [windowPulse, pulse_mul]
      rw [integral_pulse, min_eq_right (hx i hi).2, min_eq_right (hx j hj).2,
        max_eq_right (sub_nonneg.mpr (hx i hi).1), max_eq_right (sub_nonneg.mpr (hx j hj).1),
        overlap_triangle, abs_of_nonpos (sub_nonpos.mpr (hmono (by omega)))]
      exact (show h ≤ 2*h - -(x i - x j) by linarith [hc.2]).trans (le_max_left _ _)
    · simp only [term, if_neg hc, mul_zero, integral_zero, le_rfl]
  have hpoint (t : ℝ) : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, term i j t) ≤
      crowdedSquare J (windowCount (Finset.range n) x T (2*h) t) := by
    by_cases hd : (J : ℝ) < windowCount (Finset.range n) x T (2*h) t
    · rw [crowdedSquare, if_pos hd, windowCount_sq_expansion]
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hc : i + J < j ∧ x j - x i ≤ h
      · simp only [term, if_pos hc, le_rfl]
      · simpa only [term, if_neg hc] using
          mul_nonneg (wp_nonneg T (2*h) (x i) t) (wp_nonneg T (2*h) (x j) t)
    · rw [crowdedSquare, if_neg hd]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hc : i + J < j ∧ x j - x i ≤ h
      · by_cases hiw : t ∈ Ioc (max 0 (x i - 2*h)) (min T (x i))
        · by_cases hjw : t ∈ Ioc (max 0 (x j - 2*h)) (min T (x j))
          · exact (hd (rank_forces_crowding hmono (Finset.mem_range.mp hj) hc.1 hiw hjw)).elim
          · simp only [term, if_pos hc, windowPulse, pulse, Set.indicator_of_notMem hjw, mul_zero]
        · simp only [term, if_pos hc, windowPulse, pulse, Set.indicator_of_notMem hiw, zero_mul]
      · simp only [term, if_neg hc]
  calc
    h * rankTailCount n J x h ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ t, term i j t := by
      simp only [rankTailCount, Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        hmass i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    _ = ∫ t, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, term i j t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ => hterm i j)]
    _ ≤ ∫ t : ℝ, g t := integral_mono
      (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j)))
      hg (fun t => (hpoint t).trans (hdom t))

lemma sorted_window_eq_actual (T H t : ℝ) :
    windowCount (Finset.range (Ncount 0 T)) (cutoffOrdinate T) T H t = actualWindowCount T H t := by
  unfold windowCount actualWindowCount
  exact cutoffOrdinate_sum T (fun y => windowPulse T H y t)

lemma actual_window_nonneg (T H t : ℝ) : 0 ≤ actualWindowCount T H t := by
  rw [actualWindowCount_eq_card]
  positivity

lemma actual_cube_integrable (T H : ℝ) : Integrable (fun t => (actualWindowCount T H t)^3) := by
  let K := actualWindowCount T H
  have hb (t : ℝ) : K t ≤ (Fintype.card (Copies T) : ℝ) := by
    rw [show K t = (translatedWindowCard T H t : ℝ) by exact actualWindowCount_eq_card T H t]
    exact_mod_cast (show translatedWindowCard T H t ≤ Fintype.card (Copies T) from
      (Finset.card_filter_le _ _).trans_eq (Finset.card_univ))
  have hi : Integrable K := windowCount_integrable _ _ _ _
  have hi2 : Integrable (fun t => K t^2) := windowCount_sq_integrable _ _ _ _
  refine (hi2.const_mul (Fintype.card (Copies T) : ℝ)).mono' (hi.aestronglyMeasurable.pow 3)
    (ae_of_all _ fun t => ?_)
  change ‖K t ^ 3‖ ≤ (Fintype.card (Copies T) : ℝ) * (K t)^2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (actual_window_nonneg T H t) _),
    pow_succ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb t) (sq_nonneg _)

/-- At every sufficiently high cutoff the covering inequality holds for every
rank cutoff and every integrable crowded-window majorant simultaneously. -/
theorem eventually_actual_cover {q : ℝ} (hq : 0 < q) :
    ∀ᶠ T : ℝ in atTop, ∀ (J : ℕ) (g : ℝ → ℝ), Integrable g →
      (∀ t, crowdedSquare J (actualWindowCount T (2*q / (Real.log T / (2*Real.pi))) t) ≤ g t) →
      actualRankTail T q J ≤ (∫ t, g t) / (T*q) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_supported_width (2*q)] with T hT hfloor
  intro J g hg hdom
  let L := Real.log T / (2*Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have ht : 0 < T := zero_lt_one.trans hT
  have hw : 2*(q/L) = 2*q/L := by ring
  have hsup (i : ℕ) (hi : i < Ncount 0 T) :
      2*(q/L) ≤ cutoffOrdinate T i ∧ cutoffOrdinate T i ≤ T := by
    obtain ⟨c,hc⟩ := mem_chronologicalList.mp (cutoffOrdinate_mem hi)
    rw [hw, ← hc]
    exact ⟨(hfloor (2*q) (by positivity) le_rfl).2 c, (mem_cutoff.mp c.1.2).2.2⟩
  have hh := rankTailCount_cover (J := J) (cutoffOrdinate_monotone T) hsup hg
    (fun t => by rw [sorted_window_eq_actual, hw]; exact hdom t)
  have hden : normalizer T = T*L := by dsimp [normalizer,L]; ring
  unfold actualRankTail
  rw [hden]
  change rankTailCount (Ncount 0 T) J (cutoffOrdinate T) (q/L) / (T*L) ≤ (∫ t, g t)/(T*q)
  rw [div_le_div_iff₀ (mul_pos ht hL) (mul_pos ht hq)]
  have hh' := (div_le_iff₀ hL).mp (show
      (q * rankTailCount (Ncount 0 T) J (cutoffOrdinate T) (q/L)) / L ≤ ∫ t, g t by
    convert hh using 1
    ring)
  nlinarith only [mul_le_mul_of_nonneg_left hh' ht.le]

/-- The published fixed third-moment input at twice the requested width suffices.
The threshold in T is uniform in the integer rank cutoff. -/
theorem eventually_rankTail_le_third {q : ℝ} (hq : 0 < q)
    (h3 : BoundedTranslatedThirdMoment (2 * q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ J : ℕ, 0 < J →
      actualRankTail T q J ≤ C / (q * J) := by
  obtain ⟨C,hC,hthird⟩ := h3
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_actual_cover hq, hthird, eventually_gt_atTop (1:ℝ)]
    with T hcover hmoment ht
  intro J hJ
  let H := 2*q / (Real.log T/(2*Real.pi))
  let K := actualWindowCount T H
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht' : 0 < T := zero_lt_one.trans ht
  have hc := hcover J (fun t => (J:ℝ)⁻¹ * (K t)^3)
    ((actual_cube_integrable T H).const_mul ((J:ℝ)⁻¹)) (fun t => by
      change crowdedSquare J (K t) ≤ (J:ℝ)⁻¹ * (K t)^3
      by_cases hk : (J:ℝ) < K t
      · rw [crowdedSquare, if_pos hk, ← div_eq_inv_mul, le_div_iff₀ hj]
        nlinarith only [mul_le_mul_of_nonneg_left hk.le (sq_nonneg (K t))]
      · rw [crowdedSquare, if_neg hk]
        exact mul_nonneg (inv_nonneg.mpr hj.le) (pow_nonneg (actual_window_nonneg T H t) _))
  rw [integral_const_mul] at hc
  change (∫ t, (K t)^3) / T ≤ C at hmoment
  calc
    actualRankTail T q J ≤ _ := hc
    _ = ((∫ t, (K t)^3)/T) / (q*J) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hmoment (mul_pos hq hj).le

end RiemannResearch.Analysis.MicroscopicRankCover
