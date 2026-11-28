import RiemannResearch.RH.ParetoOrdinateCosineCompleteness
import RiemannResearch.RH.IntegerDPPKernel
import RiemannResearch.Analysis.MontgomeryWindowPairCorrelation
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unfolded zero pairs in the squared first-site projection error

All sums retain the actual zero occurrences. The fixed-window asymptotic uses
the sine second moment as an explicit hypothesis. Its two contributions to the
ordered pair count are the equal-height mass and the positive-gap sine integral
in both orientations. Compare Goldston, Lee, Schettler and Suriajaya, Sections
3–5 of https://arxiv.org/abs/2503.15449, for these conventions.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryPositiveGap

theorem cosineRow_norm_le_one (t : ℝ) : ‖cosineRow t‖ ≤ 1 := by
  have h : ‖cosineRow t‖ ^ 2 ≤ 1 := by
    rw [hilbert_norm_sq, ← paretoWeight_tsum]
    apply (hilbert_coordinate_square_summable _).tsum_le_tsum _ paretoWeight_hasSum.summable
    intro i
    change (Real.sqrt (paretoWeight i) * Real.cos (Real.log ((i + 1 : ℕ) : ℝ) * t)) ^ 2 ≤ _
    rw [mul_pow, Real.sq_sqrt (paretoWeight_pos i).le]
    apply mul_le_of_le_one_right (paretoWeight_pos i).le
    have hc := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_cos_le_one
      (Real.log ((i + 1 : ℕ) : ℝ) * t)) 2
    simpa only [sq_abs, one_pow] using hc
  nlinarith [norm_nonneg (cosineRow t)]

/-- Signed Gram entry after projection onto the orthogonal complement of the legal space. -/
def residualGram (t u : ℝ) : ℝ :=
  inner ℝ (closedSpaceᗮ.starProjection (cosineRow t)) (closedSpaceᗮ.starProjection (cosineRow u))

theorem abs_residualGram_le_one (t u : ℝ) : |residualGram t u| ≤ 1 := by
  have h (s : ℝ) : ‖closedSpaceᗮ.starProjection (cosineRow s)‖ ≤ 1 :=
    (closedSpaceᗮ.norm_starProjection_apply_le _).trans (cosineRow_norm_le_one _)
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul (h t) (h u) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

def squaredError (T : ℝ) : ℝ := ‖closedSpaceᗮ.starProjection (recovery T 0)‖ ^ 2

/-- The original error includes all ordered pairs, even equal heights with different labels. -/
theorem squaredError_eq_pair_sum (T : ℝ) :
    squaredError T = (∑ i : Copies T, ∑ j : Copies T,
      residualGram (copyOrdinate T i) (copyOrdinate T j)) / (Ncount 0 T : ℝ) ^ 2 := by
  rw [squaredError, recovery_zero_eq_mean, map_smul, map_sum, ← real_inner_self_eq_norm_sq]
  simp only [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  change _ = (∑ i : Copies T, ∑ j : Copies T,
    inner ℝ (closedSpaceᗮ.starProjection (cosineRow i.1.1.im))
      (closedSpaceᗮ.starProjection (cosineRow j.1.1.im))) / _
  have hswap : (∑ j : Copies T, ∑ i : Copies T,
      inner ℝ (closedSpaceᗮ.starProjection (cosineRow i.1.1.im))
        (closedSpaceᗮ.starProjection (cosineRow j.1.1.im))) =
      ∑ i : Copies T, ∑ j : Copies T,
        inner ℝ (closedSpaceᗮ.starProjection (cosineRow i.1.1.im))
          (closedSpaceᗮ.starProjection (cosineRow j.1.1.im)) := Finset.sum_comm
  rw [← Finset.mul_sum, hswap]
  ring

/-- The first-site vacancy of the discrete legal projection supplies the limiting constant. -/
theorem first_site_residual_sq :
    ‖closedSpaceᗮ.starProjection (paretoPointHilbert 0)‖ ^ 2 =
      (1 - IntegerDPP.limitingKernel 0 0) / 2 := by
  have he := IntegerDPP.first_site_projection_complement closedSpace
  change 1 - IntegerDPP.limitingKernel 0 0 =
    2 * ‖paretoPointHilbert 0 - closedSpace.starProjection (paretoPointHilbert 0)‖ ^ 2 at he
  rw [Submodule.starProjection_orthogonal_val]
  linarith only [he]

theorem squaredError_tendsto :
    Tendsto squaredError atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 2)) := by
  have ht := (closedSpaceᗮ.starProjection.continuous.continuousAt.tendsto.comp
    first_recovery_tendsto).norm.pow 2
  change Tendsto (fun T => ‖closedSpaceᗮ.starProjection (recovery T 0)‖ ^ 2) _ _
  simpa only [Function.comp_def, first_site_residual_sq] using ht

private def windowWeight (T q : ℝ) (i j : Copies T) : ℝ :=
  if |Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i)| ≤ q then 1 else 0

/-- Unweighted ordered pair count in a fixed unfolded window, including the full zero-gap mass. -/
def windowCount (T q : ℝ) : ℝ := ∑ i : Copies T, ∑ j : Copies T, windowWeight T q i j

private theorem abs_window_split (d q : ℝ) (hq : 0 ≤ q) :
    (if |d| ≤ q then (1 : ℝ) else 0) = (if d = 0 then 1 else 0) +
      (if 0 < d ∧ d ≤ q then 1 else 0) + (if 0 < -d ∧ -d ≤ q then 1 else 0) := by
  rcases lt_trichotomy d 0 with h | h | h
  · simp [abs_of_neg h, h.ne, not_lt_of_ge h.le, neg_pos.mpr h]
  · subst d
    simp [hq]
  · simp [abs_of_pos h, h.ne', not_lt_of_ge (neg_nonpos.mpr h.le), h]

theorem windowCount_eq_collision_add_positive {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    windowCount T q / (T * Real.log T / (2 * Real.pi)) =
      (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) + 2 * positiveGapMass T q := by
  let a := Real.log T / (2 * Real.pi)
  have ha : 0 < a := div_pos (Real.log_pos hT) (by positivity)
  let F (i j : Copies T) : ℝ :=
    if 0 < a * (copyOrdinate T j - copyOrdinate T i) ∧
      a * (copyOrdinate T j - copyOrdinate T i) ≤ q then 1 else 0
  have hh (i j : Copies T) : windowWeight T q i j =
      (if copyOrdinate T i = copyOrdinate T j then 1 else 0) + F i j + F j i := by
    have h0 : a * (copyOrdinate T j - copyOrdinate T i) = 0 ↔
        copyOrdinate T i = copyOrdinate T j := by
      simp only [mul_eq_zero, ha.ne', false_or, sub_eq_zero]
      exact eq_comm
    have hr : -(a * (copyOrdinate T j - copyOrdinate T i)) =
        a * (copyOrdinate T i - copyOrdinate T j) := by ring
    simpa only [windowWeight, F, h0, hr, a] using
      abs_window_split (a * (copyOrdinate T j - copyOrdinate T i)) q hq
  have hc : (∑ i : Copies T, ∑ j : Copies T,
      if copyOrdinate T i = copyOrdinate T j then (1 : ℝ) else 0) = (actualCollision T : ℝ) := by
    simp [actualCollision, OrdinateCollisionCertificate.occurrenceCollision]
  have hswap : (∑ i : Copies T, ∑ j : Copies T, F j i) = ∑ i : Copies T, ∑ j : Copies T, F i j :=
    Finset.sum_comm
  change windowCount T q / _ = _ + 2 * ((∑ i : Copies T, ∑ j : Copies T, F i j) / _)
  simp only [windowCount, hh, Finset.sum_add_distrib, hc, hswap]
  ring

/-- The two-level GUE prediction gives the order-N mass of the fixed window. -/
theorem windowCount_div_count_tendsto_of_sine (h : SineWindowMoment) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun T : ℝ => windowCount T q / (Ncount 0 T : ℝ)) atTop (𝓝 (1 + 2 * sineGapMass q)) := by
  have ht := ((collision_limit_of_sineWindowMoment h).add
    ((positiveGap_tendsto_of_sineWindowMoment h hq).const_mul 2)).div
      tendsto_count_div_mainTerm (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_count_pos] with T hT hN
  change (((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) + 2 * positiveGapMass T q) /
    ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi)))) = _
  rw [← windowCount_eq_collision_add_positive hT hq.le]
  have hd : T * Real.log T / (2 * Real.pi) ≠ 0 := (div_pos
    (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).ne'
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hd, hn, (Real.log_pos hT).ne']

def nearError (T q : ℝ) : ℝ := (∑ i : Copies T, ∑ j : Copies T,
  windowWeight T q i j * residualGram (copyOrdinate T i) (copyOrdinate T j)) / (Ncount 0 T : ℝ) ^ 2

def farError (T q : ℝ) : ℝ := (∑ i : Copies T, ∑ j : Copies T,
  (1 - windowWeight T q i j) * residualGram (copyOrdinate T i) (copyOrdinate T j)) /
    (Ncount 0 T : ℝ) ^ 2

theorem squaredError_eq_near_add_far (T q : ℝ) :
    squaredError T = nearError T q + farError T q := by
  rw [squaredError_eq_pair_sum, nearError, farError, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem abs_nearError_le (T q : ℝ) : |nearError T q| ≤ windowCount T q / (Ncount 0 T : ℝ) ^ 2 := by
  rw [nearError, abs_div, abs_of_nonneg (sq_nonneg (Ncount 0 T : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  unfold windowWeight
  split_ifs
  · simpa only [one_mul] using abs_residualGram_le_one (copyOrdinate T i) (copyOrdinate T j)
  · simp

theorem nearError_tendsto_zero_of_sine (h : SineWindowMoment) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun T => nearError T q) atTop (𝓝 0) := by
  have hinv : Tendsto (fun T : ℝ => (Ncount 0 T : ℝ)⁻¹) atTop (𝓝 0) := by
    have ht := tendsto_height_div_count.mul tendsto_inv_atTop_zero
    simp only [zero_mul] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp [hT.ne']
  have hu := (windowCount_div_count_tendsto_of_sine h hq).mul hinv
  simp only [mul_zero] at hu
  apply squeeze_zero_norm' _ hu
  exact Eventually.of_forall (fun T => by
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, mul_inv_rev, pow_two, mul_assoc] using
      abs_nearError_le T q)

theorem farError_tendsto_of_sine (h : SineWindowMoment) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun T => farError T q) atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 2)) := by
  have ht := squaredError_tendsto.sub (nearError_tendsto_zero_of_sine h hq)
  simp only [sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun T => by
    change squaredError T - nearError T q = farError T q
    rw [squaredError_eq_near_add_far T q]
    ring)

/-- The first-site squared residual vanishes exactly under the project's
Nyman–Beurling criterion for RH. -/
theorem rh_iff_first_site_vacancy_zero :
    RiemannHypothesis ↔ (1 - IntegerDPP.limitingKernel 0 0) / 2 = 0 := by
  have hRH : RiemannHypothesis ↔ paretoPointHilbert 0 ∈ closedSpace :=
    (PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.trans
      BaezDuarte.naturalApproximation_iff_one_mem).trans firstPoint_mem_iff_one_mem.symm
  rw [hRH, ← first_site_residual_sq, Submodule.starProjection_orthogonal_val]
  constructor
  · intro hm
    simp [Submodule.starProjection_eq_self_iff.mpr hm]
  · intro hz
    have he : ‖paretoPointHilbert 0 - closedSpace.starProjection (paretoPointHilbert 0)‖ = 0 := by
      nlinarith only [hz]
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

/-- Under the sine second moment, cancellation of the signed complement of
one fixed unfolded window is equivalent to RH. -/
theorem rh_iff_farError_tendsto_zero_of_sine (h : SineWindowMoment) {q : ℝ} (hq : 0 < q) :
    RiemannHypothesis ↔ Tendsto (fun T => farError T q) atTop (𝓝 0) := by
  rw [rh_iff_first_site_vacancy_zero]
  have ht := farError_tendsto_of_sine h hq
  exact ⟨fun he => he ▸ ht, tendsto_nhds_unique ht⟩

end RiemannResearch.RH.Pareto.OrdinateCosine
