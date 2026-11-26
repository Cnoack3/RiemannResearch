import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.MontgomerySampledCountError
import RiemannResearch.Analysis.ZeroDPPCollisionLoss
import RiemannResearch.Analysis.MicroscopicRankCover

/-! Strictly positive finite-index-gap statistics on the complete chronological
occurrence list. The iterated limsup criterion is the one in
RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md. -/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ZeroDPPCollisionLoss

private def ordinateGapStep (T q x y : ℝ) : ℝ :=
  if 0 < unfoldingScale T * (y - x) ∧ unfoldingScale T * (y - x) ≤ q then 1 else 0

/-- Strictly positive gaps at precisely the indicated chronological index distance.
Both endpoints belong to the true cutoff, including all coincident occurrences. -/
def positiveIndexGapMass (T q : ℝ) (d : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (Ncount 0 T), if i + d < Ncount 0 T then
    ordinateGapStep T q (cutoffOrdinate T i) (cutoffOrdinate T (i + d)) else 0) /
    normalizer T

/-- Sum of the first J finite-index-gap statistics, with the original normalization. -/
def finiteIndexGapMass (T q : ℝ) (J : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 J, positiveIndexGapMass T q d

private theorem singleRank_sum (w : ℕ → ℕ → ℝ) (i d n : ℕ) :
    (∑ j ∈ Finset.range n, if j = i + d then w i j else 0) =
      if i + d < n then w i (i + d) else 0 := by
  simp [Finset.mem_range]

private theorem ranks_at_pair (w : ℕ → ℕ → ℝ) (i j J : ℕ) :
    (∑ d ∈ Finset.Icc 1 J, if j = i + d then w i j else 0) =
      if i < j ∧ j ≤ i + J then w i j else 0 := by
  by_cases hij : i ≤ j
  · have h (d : ℕ) : (j = i + d) ↔ (d = j - i) := by omega
    simp_rw [h]
    have hk : (1 ≤ j - i ∧ j ≤ J + i) ↔ (i < j ∧ j ≤ i + J) := by omega
    simp [Finset.mem_Icc, hk]
  · have h (d : ℕ) : j ≠ i + d := by omega
    simp [h, show ¬i < j by omega]

private theorem finiteIndexGapMass_rows (T q : ℝ) (J : ℕ) :
    finiteIndexGapMass T q J =
    (∑ i ∈ Finset.range (Ncount 0 T), ∑ j ∈ Finset.range (Ncount 0 T),
      if i < j ∧ j ≤ i + J then
        ordinateGapStep T q (cutoffOrdinate T i) (cutoffOrdinate T j) else 0) /
    normalizer T := by
  let n := Ncount 0 T
  let s := Finset.range n
  let r := Finset.Icc 1 J
  let w := fun i j => ordinateGapStep T q (cutoffOrdinate T i) (cutoffOrdinate T j)
  unfold finiteIndexGapMass positiveIndexGapMass
  rw [← Finset.sum_div]
  change (∑ d ∈ r, ∑ i ∈ s, if i + d < n then w i (i + d) else 0) / _ = _
  congr 1
  calc
    _ = ∑ d ∈ r, ∑ i ∈ s, ∑ j ∈ s, if j = i + d then w i j else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_congr rfl (fun i _ => (singleRank_sum w i d n).symm)
    _ = ∑ i ∈ s, ∑ d ∈ r, ∑ j ∈ s, if j = i + d then w i j else 0 := Finset.sum_comm
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ d ∈ r, if j = i + d then w i j else 0 :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => ranks_at_pair w i j J))

private theorem sorted_positiveGapMass (T q : ℝ) :
    positiveGapMass T q =
      (∑ i ∈ Finset.range (Ncount 0 T), ∑ j ∈ Finset.range (Ncount 0 T),
        ordinateGapStep T q (cutoffOrdinate T i) (cutoffOrdinate T j)) / normalizer T := by
  change (∑ c : Copies T, ∑ d : Copies T,
    ordinateGapStep T q (copyOrdinate T c) (copyOrdinate T d)) / _ = _
  congr 1
  symm
  calc
    _ = ∑ i ∈ Finset.range (Ncount 0 T), ∑ d : Copies T,
          ordinateGapStep T q (cutoffOrdinate T i) (copyOrdinate T d) :=
      Finset.sum_congr rfl (fun i _ =>
        cutoffOrdinate_sum T (ordinateGapStep T q (cutoffOrdinate T i)))
    _ = _ := cutoffOrdinate_sum T (fun x => ∑ d : Copies T,
      ordinateGapStep T q x (copyOrdinate T d))

/-- Absolute error after truncation is bounded by the collision-inclusive rank tail. -/
theorem positiveGapMass_sub_finiteIndexGapMass_le {T : ℝ} (hT : 1 < T) (q : ℝ) (J : ℕ) :
    |positiveGapMass T q - finiteIndexGapMass T q J| ≤
      (∑ i ∈ Finset.range (Ncount 0 T), ∑ j ∈ Finset.range (Ncount 0 T),
        if i + J < j ∧ cutoffOrdinate T j - cutoffOrdinate T i ≤ q / unfoldingScale T
        then (1 : ℝ) else 0) / normalizer T := by
  let L := unfoldingScale T
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  let x := cutoffOrdinate T
  let w := fun i j => ordinateGapStep T q (x i) (x j)
  let e := fun i j => w i j - (if i < j ∧ j ≤ i + J then w i j else 0)
  have hb (i j : ℕ) : 0 ≤ e i j ∧ e i j ≤
      if i + J < j ∧ x j - x i ≤ q / L then (1 : ℝ) else 0 := by
    dsimp only [e, w]
    by_cases ha : 0 < L * (x j - x i) ∧ L * (x j - x i) ≤ q
    · have hw : ordinateGapStep T q (x i) (x j) = 1 := if_pos ha
      have hd : 0 < x j - x i := pos_of_mul_pos_right ha.1 hL.le
      have hij : i < j := by
        by_contra! h
        exact (not_lt_of_ge (cutoffOrdinate_monotone T h)) (sub_pos.mp hd)
      have hwidth : x j - x i ≤ q / L := (le_div_iff₀ hL).2 (by simpa [mul_comm] using ha.2)
      by_cases hj : j ≤ i + J
      · simp [hw, hij, hj, not_lt.mpr hj]
      · simp [hw, hij, hj, lt_of_not_ge hj, hwidth]
    · have hw : ordinateGapStep T q (x i) (x j) = 0 := if_neg ha
      simp only [hw, ite_self, sub_zero, le_rfl, true_and]
      split_ifs <;> norm_num
  rw [sorted_positiveGapMass, finiteIndexGapMass_rows, ← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  change |(∑ i ∈ Finset.range _, ∑ j ∈ Finset.range _, e i j) / normalizer T| ≤ _
  rw [abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => (hb i j).1) hD.le)]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => (hb i j).2) hD.le

private theorem singleIndex_bounds {T : ℝ} (hT : 1 < T) (q : ℝ) (d : ℕ) :
    0 ≤ positiveIndexGapMass T q d ∧ positiveIndexGapMass T q d ≤
      (Ncount 0 T : ℝ) / normalizer T := by
  have hD : 0 ≤ normalizer T :=
    (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).le
  unfold positiveIndexGapMass
  constructor
  · apply div_nonneg _ hD
    apply Finset.sum_nonneg
    intro i _
    simp only [ordinateGapStep]
    split_ifs <;> norm_num
  · apply div_le_div_of_nonneg_right _ hD
    calc
      _ ≤ ∑ _i ∈ Finset.range (Ncount 0 T), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [ordinateGapStep]
        split_ifs <;> norm_num
      _ = _ := by simp

private theorem finiteIndexError_bounded (q : ℝ) (J : ℕ) :
    (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun T => |finiteIndexGapMass T q J - sineGapMass q|) := by
  let k : ℝ := (Finset.Icc 1 J).card
  refine ⟨k * 2 + |sineGapMass q|, eventually_map.mpr ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_count_div_mainTerm.eventually_lt_const (by norm_num : (1 : ℝ) < 2)]
    with T hT hN
  have h0 : 0 ≤ finiteIndexGapMass T q J :=
    Finset.sum_nonneg (fun d _ => (singleIndex_bounds hT q d).1)
  have h2 : finiteIndexGapMass T q J ≤ k * 2 := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 J, (2 : ℝ) :=
        Finset.sum_le_sum fun d _ => (singleIndex_bounds hT q d).2.trans hN.le
      _ = _ := by simp [k]
  exact (abs_sub _ _).trans (add_le_add ((abs_of_nonneg h0).le.trans h2) le_rfl)

private theorem iterated_error_iff {p : ℝ → ℝ} {s : ℕ → ℝ → ℝ} {g : ℝ}
    (hb : ∀ J, (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (fun T => |s J T - g|))
    (htail : ∀ ε : ℝ, 0 < ε → ∀ᶠ J : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      |p T - s J T| < ε) :
    Tendsto p atTop (𝓝 g) ↔
      Tendsto (fun J : ℕ => limsup (fun T : ℝ => |s J T - g|) atTop) atTop (𝓝 0) := by
  have hlow (J : ℕ) : (atTop : Filter ℝ).IsBoundedUnder (· ≥ ·) (fun T => |s J T - g|) :=
    ⟨0, eventually_map.mpr (Eventually.of_forall fun _ => abs_nonneg _)⟩
  have hpos (J : ℕ) : 0 ≤ limsup (fun T : ℝ => |s J T - g|) atTop :=
    le_limsup_of_frequently_le
      (Eventually.of_forall (fun T => abs_nonneg (s J T - g))).frequently (hb J)
  constructor
  · intro hp
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [htail (ε / 4) (by positivity)] with J hJ
    have hlim : limsup (fun T => |s J T - g|) atTop ≤ ε / 2 := by
      apply limsup_le_of_le (hlow J).isCobounded_flip
      filter_upwards [hJ, Metric.tendsto_nhds.mp hp (ε / 4) (by positivity)] with T hT hpT
      rw [Real.dist_eq] at hpT
      rw [abs_sub_comm] at hT
      linarith only [abs_sub_le (s J T) (p T) g, hT, hpT]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos J)]
    exact hlim.trans_lt (half_lt_self hε)
  · intro hs
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨J, hJ, hsl⟩ := ((htail (ε / 2) (half_pos hε)).and
      (hs.eventually_lt_const (half_pos hε))).exists
    filter_upwards [hJ, eventually_lt_of_limsup_lt hsl (hb J)] with T hT hS
    rw [Real.dist_eq]
    linarith only [abs_sub_le (p T) (s J T) g, hT, hS]

/-- The inner height operation is a limsup of absolute aggregate errors.
It requires no limit for an individual index spacing. -/
theorem positiveGapPCC_iff_finiteIndexGap_limsup
    (htail : ∀ q : ℚ, 0 < q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ J : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
        |positiveGapMass T q - finiteIndexGapMass T q J| < ε) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun J : ℕ => limsup
        (fun T : ℝ => |finiteIndexGapMass T q J - sineGapMass q|) atTop) atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_rationalWidthLimits]
  constructor
  · intro h q hq
    exact (iterated_error_iff (finiteIndexError_bounded q) (htail q hq)).mp (h q hq)
  · intro h q hq
    exact (iterated_error_iff (finiteIndexError_bounded q) (htail q hq)).mpr (h q hq)

/-- For the iterated criterion the threshold height may depend on the
fixed rank J. No assertion about a simultaneous moving cutoff is used. -/
theorem iteratedRankError_of_inverse_rank {err : ℕ → ℝ → ℝ} {C : ℝ}
    (h : ∀ J : ℕ, 0 < J → ∀ᶠ T : ℝ in atTop, err J T ≤ C / (J : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ J : ℕ in atTop, ∀ᶠ T : ℝ in atTop, err J T < ε := by
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_gt (max 0 (C / ε))
  filter_upwards [eventually_ge_atTop j] with J hJ
  have hJ' : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hpos : (0 : ℝ) < J := ((le_max_left 0 (C / ε)).trans_lt hj).trans_le hJ'
  have hsmall : C / (J : ℝ) < ε := (div_lt_iff₀ hpos).2 (by
    have he := (div_lt_iff₀ hε).1 (((le_max_right 0 (C / ε)).trans_lt hj).trans_le hJ')
    simpa [mul_comm] using he)
  exact (h J (by exact_mod_cast hpos)).mono (fun _ ht => ht.trans_lt hsmall)

/-- The finite-index statistic is a genuine lower truncation of the positive
two-point count. Equal-height pairs have zero weight on both sides. -/
theorem finiteIndexGapMass_le_positiveGapMass {T : ℝ} (hT : 1 < T) (q : ℝ) (J : ℕ) :
    finiteIndexGapMass T q J ≤ positiveGapMass T q := by
  rw [finiteIndexGapMass_rows, sorted_positiveGapMass]
  have hD : 0 ≤ normalizer T :=
    (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).le
  apply div_le_div_of_nonneg_right _ hD
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases h : i < j ∧ j ≤ i + J
  · simp only [if_pos h, le_rfl]
  · simp only [if_neg h, ordinateGapStep]
    split_ifs <;> norm_num

/-- Taking at least as many ranks as there are occurrences recovers the full
finite-height count. The padded ordinate after the cutoff never enters. -/
theorem finiteIndexGapMass_eq_positiveGapMass_of_count_le {T : ℝ} (hT : 1 < T)
    (q : ℝ) {J : ℕ} (hJ : Ncount 0 T ≤ J) :
    finiteIndexGapMass T q J = positiveGapMass T q := by
  have hz : (∑ i ∈ Finset.range (Ncount 0 T), ∑ j ∈ Finset.range (Ncount 0 T),
      if i + J < j ∧ cutoffOrdinate T j - cutoffOrdinate T i ≤ q / unfoldingScale T
      then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hs : ¬ i + J < j := by omega
    simp [hs]
  have he := positiveGapMass_sub_finiteIndexGapMass_le hT q J
  rw [hz, zero_div] at he
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))).symm


open MicroscopicRankCover ZeroDPPVacancyDensity

theorem positiveGapPCC_iff_finiteIndexGap_of_third
    (hm : ∀ q : ℚ, 0 < q → BoundedTranslatedThirdMoment (2 * (q : ℝ))) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun J : ℕ => limsup
        (fun T : ℝ => |finiteIndexGapMass T q J - sineGapMass q|) atTop) atTop (𝓝 0) := by
  apply positiveGapPCC_iff_finiteIndexGap_limsup
  intro q hq
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨C,_,hC⟩ := eventually_rankTail_le_third hqr (hm q hq)
  apply iteratedRankError_of_inverse_rank (C := C/(q : ℝ))
  intro J hJ
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  calc
    |positiveGapMass T q - finiteIndexGapMass T q J| ≤ actualRankTail T q J :=
      positiveGapMass_sub_finiteIndexGapMass_le hT1 q J
    _ ≤ _ := (hT J hJ).trans_eq (div_div C (q : ℝ) (J : ℝ)).symm

end RiemannResearch.Analysis.MontgomeryPositiveGap
