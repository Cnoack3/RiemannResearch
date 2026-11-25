import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import RiemannResearch.Analysis.ActualZeroAbelPairing
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Macroscopic positive gaps of the actual zeta-zero ordinates

At a fixed fraction of the entire unfolded height the positive pair count
has a triangular limit. This follows from uniform convergence of the scaled
one-point counting function. The finite comparison below keeps the two
endpoint counts for each row, so multiple zeros and equal ordinates retain
their actual multiplicities.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

/-- Full unfolded cutoff and zero-count normalization. -/
def unfoldedCutoff (T : ℝ) : ℝ := T * Real.log T / (2 * Real.pi)

private theorem unfoldedCutoff_pos {T : ℝ} (hT : 1 < T) : 0 < unfoldedCutoff T :=
  div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)

/-- Cumulative height count in unfolded-cutoff normalization. -/
def scaledHeightCount (T x : ℝ) : ℝ := (Ncount 0 (x * T) : ℝ) / unfoldedCutoff T

private theorem scaledHeightCount_mono {T : ℝ} (hT : 1 < T) : Monotone (scaledHeightCount T) := by
  intro x y h
  apply div_le_div_of_nonneg_right _ (unfoldedCutoff_pos hT).le
  have hn := Ncount_mono (a := 0) le_rfl (mul_le_mul_of_nonneg_right h (zero_le_one.trans hT.le))
  exact_mod_cast hn

theorem scaledHeightCount_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun T => scaledHeightCount T x) atTop (𝓝 x) := by
  rcases hx.eq_or_lt with rfl | hx
  · have hz : cutoff 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact (not_lt_of_ge (mem_cutoff.mp hz).2.2) (mem_cutoff.mp hz).2.1
    have hn : Ncount 0 0 = 0 := by simp [count_eq_sum, hz]
    simp [scaledHeightCount, hn]
  · have hxt : Tendsto (fun T : ℝ => x * T) atTop atTop :=
      tendsto_id.const_mul_atTop hx
    have hlog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hratio : Tendsto (fun T : ℝ => x * (1 + Real.log x * (Real.log T)⁻¹)) atTop (𝓝 x) := by
      simpa only [mul_zero, add_zero, mul_one, Function.comp_def] using
        ((tendsto_const_nhds (x := (1 : ℝ))).add (hlog.const_mul (Real.log x))).const_mul x
    have ht := (tendsto_count_div_mainTerm.comp hxt).mul hratio
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hxt.eventually_gt_atTop 1] with T hT hxT
    change ((Ncount 0 (x*T) : ℝ) / unfoldedCutoff (x*T)) *
      (x*(1 + Real.log x * (Real.log T)⁻¹)) = scaledHeightCount T x
    have hlogXT := Real.log_mul hx.ne' (zero_lt_one.trans hT).ne'
    have hne := (Real.log_pos hxT).ne'
    have hne' := (Real.log_pos hT).ne'
    unfold scaledHeightCount unfoldedCutoff
    field_simp [Real.pi_ne_zero, hx.ne', (zero_lt_one.trans hT).ne', hne, hne']
    rw [hlogXT]
    ring

/-- Uniformity down to height zero follows from monotonicity of the normalized
count and the continuous linear height limit. -/
theorem eventually_scaledHeightCount_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (0 : ℝ) 1, |scaledHeightCount T x - x| ≤ ε := by
  classical
  let d := ε / 3
  have hd : 0 < d := by dsimp [d]; linarith
  let U := fun x : Icc (0 : ℝ) 1 => Ioo ((x : ℝ)-d) ((x : ℝ)+d)
  have cover : Icc (0 : ℝ) 1 ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, by change x-d < x ∧ x < x+d; constructor <;> linarith⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) cover
  have he : ∀ᶠ T : ℝ in atTop, ∀ x ∈ s,
      |scaledHeightCount T (max 0 ((x : ℝ)-d)) - max 0 ((x : ℝ)-d)| < d ∧
      |scaledHeightCount T ((x : ℝ)+d) - ((x : ℝ)+d)| < d := by
    apply (Filter.eventually_all_finset s).mpr
    intro x _
    have hl := Metric.tendsto_nhds.mp (scaledHeightCount_tendsto (le_max_left 0 ((x : ℝ)-d))) d hd
    have hr := Metric.tendsto_nhds.mp (scaledHeightCount_tendsto (add_nonneg x.2.1 hd.le)) d hd
    simpa only [Real.dist_eq] using hl.and hr
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T h T₀
  intro u hu
  obtain ⟨x,hxu⟩ := mem_iUnion.mp (hs hu)
  obtain ⟨hx,hux⟩ := mem_iUnion.mp hxu
  change (x : ℝ)-d < u ∧ u < (x : ℝ)+d at hux
  have hl := scaledHeightCount_mono T₀ (max_le hu.1 hux.1.le)
  have hr := scaledHeightCount_mono T₀ hux.2.le
  have hleft := (abs_lt.mp (h x hx).1).1
  have hright := (abs_lt.mp (h x hx).2).2
  have hm := le_max_right (0 : ℝ) ((x : ℝ)-d)
  dsimp only [d] at *
  exact abs_le.mpr ⟨by linarith only [hl, hleft, hm, hux.2], by linarith only [hr, hright, hux.1]⟩

/-- Every cumulative count below the cutoff is an exact sum over its multiplicity copies. -/
theorem cumulative_copy_steps {T s : ℝ} (hs : s ≤ T) :
    (Ncount 0 s : ℝ) = ∑ i : Copies T, if copyOrdinate T i ≤ s then (1 : ℝ) else 0 := by
  classical
  rw [count_eq_sum, ActualZeroAbelPairing.cutoff_eq_filter hs, Nat.cast_sum, Finset.sum_filter]
  unfold copyOrdinate
  rw [← realSum_eq_copies T (fun z => if z.im ≤ s then (1 : ℝ) else 0)]
  unfold realSum
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : z.im ≤ s <;> simp [h]

private def heightStep (v x : ℝ) : ℝ := if v ≤ x then 1 else 0

private theorem heightStep_integral {a v : ℝ} (ha : a ≤ 1) (hv : v ≤ 1) :
    (∫ x in a..1, heightStep v x) = 1 - max a v := by
  have hfun : heightStep v = (Ici v).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases h : v ≤ x <;> simp [heightStep, Set.indicator, h]
  rw [hfun, intervalIntegral.integral_of_le ha, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  by_cases h : v ≤ a
  · have hi : Ici v ∩ Ioc a 1 = Ioc a 1 := inter_eq_right.mpr (fun x hx => h.trans hx.1.le)
    rw [hi, max_eq_left h, ← intervalIntegral.integral_of_le ha]
    simp
  · have hav : a < v := lt_of_not_ge h
    have hi : Ici v ∩ Ioc a 1 = Icc v 1 := by
      ext x
      change (v ≤ x ∧ a < x ∧ x ≤ 1) ↔ v ≤ x ∧ x ≤ 1
      exact ⟨fun hh => ⟨hh.1,hh.2.2⟩, fun hh => ⟨hh.1,hav.trans_le hh.1,hh.2⟩⟩
    rw [hi, max_eq_right hav.le, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv]
    simp

private theorem heightStep_mono (v : ℝ) : Monotone (heightStep v) := by
  intro x y hxy
  by_cases hx : v ≤ x
  · simp [heightStep, hx, hx.trans hxy]
  · simp [heightStep, hx]; split <;> norm_num

private theorem scaledHeightCount_steps {T x : ℝ} (hT : 1 < T) (hx : x ≤ 1) :
    scaledHeightCount T x =
      (∑ i : Copies T, heightStep (copyOrdinate T i / T) x) / unfoldedCutoff T := by
  have ht := zero_lt_one.trans hT
  rw [scaledHeightCount, cumulative_copy_steps (by simpa using mul_le_mul_of_nonneg_right hx ht.le)]
  simp only [heightStep, div_le_iff₀ ht]

/-- The complete row of strictly positive gaps is a difference of two actual
cumulative height counts. The lower endpoint removes all equal ordinates. -/
theorem positiveGapMass_scaled_eq_height_rows {T c : ℝ} (hT : 1 < T) (hc : 0 ≤ c) :
    positiveGapMass T (c * unfoldedCutoff T) =
      ∑ i : Copies T, (scaledHeightCount T (min 1 (copyOrdinate T i / T + c)) -
        scaledHeightCount T (copyOrdinate T i / T)) := by
  classical
  let t := copyOrdinate T
  let L := Real.log T / (2 * Real.pi)
  have hT₀ := zero_lt_one.trans hT
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hx (i : Copies T) : t i / T ≤ 1 := by
    apply (div_le_iff₀ hT₀).mpr
    rw [one_mul]
    exact (mem_cutoff.mp i.1.property).2.2
  change (∑ i : Copies T, ∑ j : Copies T,
    if 0 < L * (t j - t i) ∧ L * (t j - t i) ≤ c * unfoldedCutoff T then (1 : ℝ) else 0) /
    unfoldedCutoff T = _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [scaledHeightCount_steps hT (min_le_left _ _), scaledHeightCount_steps hT (hx i),
    ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h1 : 0 < L * (t j - t i) ↔ t i / T < t j / T := by
    rw [mul_pos_iff_of_pos_left hL, sub_pos, div_lt_div_iff_of_pos_right hT₀]
  have h2 : L * (t j - t i) ≤ c * unfoldedCutoff T ↔ t j / T ≤ min 1 (t i / T + c) := by
    have hD : c * unfoldedCutoff T = L * (c * T) := by dsimp only [L,unfoldedCutoff]; ring
    rw [hD, mul_le_mul_iff_right₀ hL, le_min_iff, and_iff_right (hx j),
      div_le_iff₀ hT₀, add_mul, div_mul_cancel₀ _ hT₀.ne']
    constructor <;> intro h <;> linarith only [h]
  change (if _ ∧ _ then (1 : ℝ) else 0) =
    heightStep (t j / T) (min 1 (t i / T + c)) - heightStep (t j / T) (t i / T)
  simp only [h1,h2]
  by_cases hh : t j / T ≤ t i / T
  · have hh' := le_min (hx j) (hh.trans (le_add_of_nonneg_right hc))
    simp [heightStep,hh,hh',not_lt.mpr hh]
  · have hh' : t i / T < t j / T := lt_of_not_ge hh
    simp [heightStep,hh,hh']

private theorem clipped_row_integral {T c : ℝ} (hT : 1 < T) (hc : 0 ≤ c) :
    (∑ i : Copies T, (min 1 (copyOrdinate T i / T + c) - copyOrdinate T i / T)) /
      unfoldedCutoff T = ∫ x in (1-c)..1, scaledHeightCount T x := by
  classical
  have ht := zero_lt_one.trans hT
  have ha : 1 - c ≤ 1 := sub_le_self _ hc
  have hx (i : Copies T) : copyOrdinate T i / T ≤ 1 := by
    apply (div_le_iff₀ ht).mpr
    rw [one_mul]
    exact (mem_cutoff.mp i.1.property).2.2
  have hI : (∫ x in (1-c)..1, scaledHeightCount T x) =
      ∫ x in (1-c)..1,
        (∑ i : Copies T, heightStep (copyOrdinate T i / T) x) / unfoldedCutoff T := by
    apply intervalIntegral.integral_congr
    intro x hxx
    rw [uIcc_of_le ha] at hxx
    exact scaledHeightCount_steps hT hxx.2
  rw [hI, intervalIntegral.integral_div, intervalIntegral.integral_finsetSum
    (fun i _ => (heightStep_mono (copyOrdinate T i / T)).intervalIntegrable)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [heightStep_integral ha (hx i)]
  by_cases h : copyOrdinate T i / T + c ≤ 1
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_left (le_of_not_ge h), max_eq_right (by linarith)]

/-- The finite macroscopic gap discrepancy is bounded by the uniform error
of the one-point cumulative height law. -/
theorem macroscopic_gap_error_le {T c ε : ℝ} (hT : 1 < T) (hc : c ∈ Icc (0 : ℝ) 1)
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, |scaledHeightCount T x - x| ≤ ε) :
    |positiveGapMass T (c * unfoldedCutoff T) / unfoldedCutoff T - (c - c^2/2)| ≤
      (2 * ((Ncount 0 T : ℝ) / unfoldedCutoff T) + c) * ε := by
  classical
  let D := unfoldedCutoff T
  let x := fun i : Copies T => copyOrdinate T i / T
  let y := fun i : Copies T => min 1 (x i + c)
  let F := scaledHeightCount T
  have ht := zero_lt_one.trans hT
  have hD : 0 < D := unfoldedCutoff_pos hT
  have hx (i : Copies T) : x i ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (mem_cutoff.mp i.1.property).2.1.le ht.le,
      (div_le_iff₀ ht).mpr (by rw [one_mul]; exact (mem_cutoff.mp i.1.property).2.2)⟩
  have hy (i : Copies T) : y i ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min zero_le_one (add_nonneg (hx i).1 hc.1), min_le_left _ _⟩
  have hp := positiveGapMass_scaled_eq_height_rows hT hc.1
  change positiveGapMass T (c*D) = ∑ i : Copies T, (F (y i) - F (x i)) at hp
  have hrow (i : Copies T) : |(F (y i) - F (x i)) - (y i - x i)| ≤ 2 * ε := by
    have h1 := abs_le.mp (hF _ (hx i))
    have h2 := abs_le.mp (hF _ (hy i))
    dsimp only [F]
    exact abs_le.mpr ⟨by linarith only [h2.1,h1.2], by linarith only [h2.2,h1.1]⟩
  have hrows : |positiveGapMass T (c*D) - (∑ i : Copies T, (y i - x i))| ≤
      (Ncount 0 T : ℝ) * (2 * ε) := by
    rw [hp, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum fun i _ => hrow i).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul])
  have ha : 1-c ≤ 1 := sub_le_self _ hc.1
  have intF := (scaledHeightCount_mono hT).intervalIntegrable (a := 1-c) (b := 1) (μ := volume)
  have hfl := intervalIntegral.integral_mono_on (μ := volume) ha
    (f := fun x : ℝ => x-ε) ((continuous_id.sub continuous_const).intervalIntegrable _ _) intF
    (fun u hu => by
      have h := (abs_le.mp (hF u ⟨(sub_nonneg.mpr hc.2).trans hu.1,hu.2⟩)).1
      linarith)
  have hfu := intervalIntegral.integral_mono_on (μ := volume) ha intF (g := fun x : ℝ => x+ε)
    ((continuous_id.add continuous_const).intervalIntegrable _ _)
    (fun u hu => by
      have h := (abs_le.mp (hF u ⟨(sub_nonneg.mpr hc.2).trans hu.1,hu.2⟩)).2
      linarith)
  rw [intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ => ε)
    (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const] at hfl
  rw [intervalIntegral.integral_add (f := fun u : ℝ => u) (g := fun _ => ε)
    (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const] at hfu
  simp only [smul_eq_mul] at hfl hfu
  have hclose : |(∫ u in (1-c)..1, F u) - (c-c^2/2)| ≤ c*ε := by
    dsimp only [F]
    exact abs_le.mpr ⟨by nlinarith only [hfl], by nlinarith only [hfu]⟩
  have happrox : |positiveGapMass T (c*D) / D - ∫ u in (1-c)..1, F u| ≤
      (Ncount 0 T : ℝ)/D * (2*ε) := by
    rw [← clipped_row_integral hT hc.1, ← sub_div, abs_div, abs_of_pos hD]
    exact (div_le_div_of_nonneg_right hrows hD.le).trans_eq (by ring)
  change |positiveGapMass T (c*D) / D - (c - c^2/2)| ≤ _
  calc
    _ ≤ |positiveGapMass T (c*D) / D - ∫ u in (1-c)..1, F u| +
        |(∫ u in (1-c)..1, F u) - (c-c^2/2)| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add happrox hclose).trans_eq (by dsimp only [D]; ring)

/-- At every fraction of the full unfolded height, the macroscopic mass of
strictly positive gaps converges uniformly to the triangular distribution. -/
theorem eventually_macroscopic_gap_uniform {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ c ∈ Icc (0 : ℝ) 1,
      |positiveGapMass T (c * unfoldedCutoff T) / unfoldedCutoff T - (c - c^2/2)| ≤ η := by
  filter_upwards [eventually_scaledHeightCount_uniform (by linarith : 0 < η/5),
    tendsto_count_div_mainTerm.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    eventually_gt_atTop (1 : ℝ)] with T hF hN hT
  intro c hc
  apply (macroscopic_gap_error_le hT hc hF).trans
  change (Ncount 0 T : ℝ) / unfoldedCutoff T < 2 at hN
  have h : 2 * ((Ncount 0 T : ℝ) / unfoldedCutoff T) + c ≤ 5 := by linarith only [hN,hc.2]
  exact (mul_le_mul_of_nonneg_right h (by linarith : 0 ≤ η/5)).trans_eq (by ring)

end RiemannResearch.Analysis.MontgomeryPositiveGap
