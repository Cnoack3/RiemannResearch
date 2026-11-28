import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import RiemannResearch.RH.ParetoOrdinateInghamRecovery
import Mathlib.Tactic.Ring

/-! # Signed Pareto residual correlations on separated zero-height intervals

Counting all occurrences up to height T fixes the normalization for both
intervals. Riemann–von Mangoldt supplies their relative masses. Strong
first-site recovery then determines the signed residual correlation on each
rectangle of positive relative heights. Vanishing on one pair of disjoint
quarter intervals is equivalent to RH.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis
open ActualZeroOrdinate MontgomeryPositiveGap

private theorem relative_count_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun T : ℝ => (Ncount 0 (x * T) : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 x) := by
  have h := (scaledHeightCount_tendsto hx).div
    (scaledHeightCount_tendsto (zero_le_one : (0 : ℝ) ≤ 1)) one_ne_zero
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_count_pos] with T hT hN
  have hU : unfoldedCutoff T ≠ 0 := by
    unfold unfoldedCutoff
    exact (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).ne'
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  change scaledHeightCount T x / scaledHeightCount T 1 = _
  simp only [scaledHeightCount, one_mul]
  field_simp [hU, hn]

/-- Difference of cumulative estimators on (aT,bT], with the total count at T. -/
def heightBand (F : ℝ → ThresholdHilbert) (a b T : ℝ) : ThresholdHilbert :=
  ((Ncount 0 (b * T) : ℝ) / (Ncount 0 T : ℝ)) • F (b * T) -
    ((Ncount 0 (a * T) : ℝ) / (Ncount 0 T : ℝ)) • F (a * T)

theorem heightBand_tendsto {F : ℝ → ThresholdHilbert} {v : ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 v)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (heightBand F a b) atTop (𝓝 ((b - a) • v)) := by
  have top (x : ℝ) (hx : 0 < x) : Tendsto (fun T : ℝ => x * T) atTop atTop :=
    tendsto_id.const_mul_atTop hx
  have h := ((relative_count_tendsto hb.le).smul (hF.comp (top b hb))).sub
    ((relative_count_tendsto ha.le).smul (hF.comp (top a ha)))
  change Tendsto (fun T => heightBand F a b T) atTop _
  simpa only [heightBand, Function.comp_def, sub_smul] using h

/-- Signed inner product between two residual height bands. -/
def bandGram (F : ℝ → ThresholdHilbert) (a b c d T : ℝ) : ℝ :=
  inner ℝ (closedSpaceᗮ.starProjection (heightBand F a b T))
    (closedSpaceᗮ.starProjection (heightBand F c d T))

theorem bandGram_tendsto {F : ℝ → ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 (paretoPointHilbert 0)))
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Tendsto (bandGram F a b c d) atTop
      (𝓝 ((b - a) * (d - c) * ((1 - IntegerDPP.limitingKernel 0 0) / 2))) := by
  have hp := closedSpaceᗮ.starProjection.continuous
  have h := (hp.continuousAt.tendsto.comp (heightBand_tendsto hF ha hb)).inner
    (𝕜 := ℝ) (hp.continuousAt.tendsto.comp (heightBand_tendsto hF hc hd))
  change Tendsto (fun T => bandGram F a b c d T) atTop _
  rw [mul_comm (b - a) (d - c)]
  simpa only [Function.comp_def, bandGram, map_smul, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, first_site_residual_sq, mul_assoc] using h

private theorem cumulative_scalar {T U : ℝ} (hUT : U ≤ T) (f : ℝ → ℝ) :
    (∑ i : Copies T, if copyOrdinate T i ≤ U then f (copyOrdinate T i) else 0) =
      ∑ i : Copies U, f (copyOrdinate U i) := by
  classical
  unfold copyOrdinate
  rw [← realSum_eq_copies T (fun z => if z.im ≤ U then f z.im else 0),
    ← realSum_eq_copies U (fun z => f z.im)]
  simp only [realSum, ActualZeroAbelPairing.cutoff_eq_filter hUT, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : z.im ≤ U <;> simp [h]

private theorem count_smul_recovery (U : ℝ) :
    (Ncount 0 U : ℝ) • recovery U 0 = ∑ i : Copies U, cosineRow (copyOrdinate U i) := by
  rw [recovery_zero_eq_mean, smul_smul]
  by_cases hz : Ncount 0 U = 0
  · let : IsEmpty (Copies U) := Fintype.card_eq_zero_iff.mp ((card_copies U).trans hz)
    simp [hz]
  · have hn : (Ncount 0 U : ℝ) ≠ 0 := by exact_mod_cast hz
    rw [mul_inv_cancel₀ hn, one_smul]
    rfl

private theorem counted_prefix_eq_sum {T U : ℝ} (hUT : U ≤ T) :
    ((Ncount 0 U : ℝ) / (Ncount 0 T : ℝ)) • recovery U 0 =
      (Ncount 0 T : ℝ)⁻¹ • ∑ i : Copies T,
        (if copyOrdinate T i ≤ U then (1 : ℝ) else 0) • cosineRow (copyOrdinate T i) := by
  rw [div_eq_mul_inv, mul_comm, ← smul_smul, count_smul_recovery]
  congr 1
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ite_mul, one_mul, zero_mul]
  exact (cumulative_scalar hUT (fun t => cosineRow t k)).symm

/-- Indicator of an actual half-open interval of zero heights. -/
def bandWeight (a b t : ℝ) : ℝ := if a < t ∧ t ≤ b then 1 else 0

private theorem weight_diff {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (if t ≤ b then (1 : ℝ) else 0) - (if t ≤ a then 1 else 0) = bandWeight a b t := by
  by_cases h : t ≤ a
  · simp [h, h.trans hab, bandWeight, not_lt_of_ge h]
  · by_cases k : t ≤ b <;> simp [h, k, bandWeight, lt_of_not_ge h]

theorem actual_heightBand_eq_sum {a b T : ℝ} (hab : a ≤ b) (hb : b ≤ 1) (hT : 0 ≤ T) :
    heightBand (fun U => recovery U 0) a b T =
      (Ncount 0 T : ℝ)⁻¹ • ∑ i : Copies T,
        bandWeight (a * T) (b * T) (copyOrdinate T i) • cosineRow (copyOrdinate T i) := by
  have hba : a * T ≤ b * T := mul_le_mul_of_nonneg_right hab hT
  have hbT : b * T ≤ T := (mul_le_mul_of_nonneg_right hb hT).trans_eq (one_mul T)
  rw [heightBand, counted_prefix_eq_sum hbT, counted_prefix_eq_sum (hba.trans hbT),
    ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_smul, weight_diff hba]

/-- Bilinearity expands the interval statistic for any continuous linear map on the rows. -/
theorem projected_bands_eq_pair_sum (Q : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    {a b c d T : ℝ} (hab : a ≤ b) (hb : b ≤ 1)
    (hcd : c ≤ d) (hd : d ≤ 1) (hT : 0 ≤ T) :
    inner ℝ (Q (heightBand (fun U => recovery U 0) a b T))
      (Q (heightBand (fun U => recovery U 0) c d T)) =
      (∑ i : Copies T, ∑ j : Copies T,
        bandWeight (a * T) (b * T) (copyOrdinate T i) *
        bandWeight (c * T) (d * T) (copyOrdinate T j) *
        inner ℝ (Q (cosineRow (copyOrdinate T i))) (Q (cosineRow (copyOrdinate T j)))) /
        (Ncount 0 T : ℝ)^2 := by
  let r (i : Copies T) := Q (cosineRow (copyOrdinate T i))
  have hi (v w : Copies T → ℝ) :
      inner ℝ (∑ i, v i • r i) (∑ j, w j • r j) =
        ∑ i, ∑ j, (v i * w j) * inner ℝ (r i) (r j) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_right, mul_assoc]
  rw [actual_heightBand_eq_sum hab hb hT, actual_heightBand_eq_sum hcd hd hT,
    map_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [map_sum, map_smul]
  rw [hi]
  ring

/-- Exact double sum over the original multiplicity labels in the two bands. -/
theorem actual_bandGram_eq_pair_sum {a b c d T : ℝ} (hab : a ≤ b) (hb : b ≤ 1)
    (hcd : c ≤ d) (hd : d ≤ 1) (hT : 0 ≤ T) :
    bandGram (fun U => recovery U 0) a b c d T =
      (∑ i : Copies T, ∑ j : Copies T,
        bandWeight (a * T) (b * T) (copyOrdinate T i) *
        bandWeight (c * T) (d * T) (copyOrdinate T j) *
        residualGram (copyOrdinate T i) (copyOrdinate T j)) / (Ncount 0 T : ℝ)^2 := by
  exact projected_bands_eq_pair_sum closedSpaceᗮ.starProjection hab hb hcd hd hT

/-- One fixed pair of intervals with physical separation at least T/4. -/
def separatedGram (T : ℝ) : ℝ :=
  bandGram (fun U => recovery U 0) (1/4) (1/2) (3/4) 1 T

theorem separatedGram_tendsto :
    Tendsto separatedGram atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 32)) := by
  have h := bandGram_tendsto first_recovery_tendsto
    (show (0 : ℝ) < 1/4 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)
    (show (0 : ℝ) < 3/4 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hq (x : ℝ) : (1/2-1/4 : ℝ) * (1-3/4) * (x/2) = x/32 := by ring
  change Tendsto (bandGram (fun U => recovery U 0) (1/4) (1/2) (3/4) 1) atTop _
  simpa only [hq] using h

/-- The same rectangle has the same limit for the centered arithmetic Landau traces. -/
theorem separatedLandauGram_tendsto :
    Tendsto (bandGram (fun U => landauHead U ⌊U⌋₊) (1/4) (1/2) (3/4) 1)
      atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 32)) := by
  have h := bandGram_tendsto landauHead_tendsto_of_ingham
    (show (0 : ℝ) < 1/4 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)
    (show (0 : ℝ) < 3/4 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hq (x : ℝ) : (1/2-1/4 : ℝ) * (1-3/4) * (x/2) = x/32 := by ring
  simpa only [hq] using h

theorem rh_iff_separatedGram_tendsto_zero :
    RiemannHypothesis ↔ Tendsto separatedGram atTop (𝓝 0) := by
  constructor
  · intro h
    have hz := rh_iff_first_site_vacancy_zero.mp h
    have h32 : (1 - IntegerDPP.limitingKernel 0 0) / 32 = 0 := by linarith only [hz]
    simpa only [h32] using separatedGram_tendsto
  · intro h
    have h32 := tendsto_nhds_unique separatedGram_tendsto h
    exact rh_iff_first_site_vacancy_zero.mpr (by linarith only [h32])

/-- Arbitrarily late, arbitrarily small upper bounds on this signed statistic suffice. -/
theorem rh_iff_separatedGram_frequently_small :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ T : ℝ in atTop, separatedGram T < ε := by
  constructor
  · intro h ε hε
    exact ((rh_iff_separatedGram_tendsto_zero.mp h).eventually_lt_const hε).frequently
  · intro h
    apply rh_iff_first_site_vacancy_zero.mpr
    by_contra hn
    have hpos : 0 < (1 - IntegerDPP.limitingKernel 0 0) / 2 := by
      rw [← first_site_residual_sq]
      exact lt_of_le_of_ne (sq_nonneg _)
        (Ne.symm (by simpa only [first_site_residual_sq] using hn))
    have hp : 0 < (1 - IntegerDPP.limitingKernel 0 0) / 64 := by linarith only [hpos]
    have hl : (1 - IntegerDPP.limitingKernel 0 0) / 64 <
        (1 - IntegerDPP.limitingKernel 0 0) / 32 := by linarith only [hpos]
    exact (h _ hp) ((separatedGram_tendsto.eventually_const_lt hl).mono
      (fun _ hT => not_lt_of_ge hT.le))

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.actual_bandGram_eq_pair_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms actual_bandGram_eq_pair_sum

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_separatedGram_frequently_small' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_separatedGram_frequently_small

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.separatedLandauGram_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms separatedLandauGram_tendsto

/-- Finite-height first-site estimator error from Selberg density at exponent two. -/
def selbergTwoRadius (U C : ℝ) : ℝ :=
  Real.sqrt (24 * ((U / (Ncount 0 U : ℝ)) * (2 * C / (3 * Real.log U)))^2 +
    1 / ((⌊U⌋₊ : ℝ) + 1))

private theorem estimator_dist_le_radius {U C : ℝ} (hU : 1 < U)
    (hN : 0 < Ncount 0 U) (hC : 0 ≤ C) (hD : SelbergDensityBound U C 2) :
    ‖recovery U 0 - landauHead U ⌊U⌋₊‖ ≤ selbergTwoRadius U C := by
  have h := landauHead_distance_sq_le_of_selberg_two hU hN hC hD ⌊U⌋₊
    (Nat.floor_le (zero_le_one.trans hU.le))
  simpa only [selbergTwoRadius, Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h

/-- Selberg(2) at just the two endpoints controls replacement of a whole band. -/
theorem selberg_two_heightBand_bound {a b T C : ℝ} (hC : 0 ≤ C)
    (ha : 1 < a * T) (hb : 1 < b * T)
    (hNa : 0 < Ncount 0 (a * T)) (hNb : 0 < Ncount 0 (b * T))
    (hDa : SelbergDensityBound (a * T) C 2) (hDb : SelbergDensityBound (b * T) C 2) :
    ‖heightBand (fun U => recovery U 0) a b T -
      heightBand (fun U => landauHead U ⌊U⌋₊) a b T‖ ≤
        (Ncount 0 (b * T) : ℝ) / (Ncount 0 T : ℝ) * selbergTwoRadius (b * T) C +
        (Ncount 0 (a * T) : ℝ) / (Ncount 0 T : ℝ) * selbergTwoRadius (a * T) C := by
  let w (x : ℝ) := (Ncount 0 (x * T) : ℝ) / (Ncount 0 T : ℝ)
  let e (x : ℝ) := recovery (x * T) 0 - landauHead (x * T) ⌊x * T⌋₊
  have hw (x : ℝ) : 0 ≤ w x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have he : heightBand (fun U => recovery U 0) a b T -
      heightBand (fun U => landauHead U ⌊U⌋₊) a b T = w b • e b - w a • e a := by
    dsimp only [heightBand, w, e]
    simp only [smul_sub]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (hw b), abs_of_nonneg (hw a)]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (estimator_dist_le_radius hb hNb hC hDb) (hw b))
    (mul_le_mul_of_nonneg_left (estimator_dist_le_radius ha hNa hC hDa) (hw a))

end RiemannResearch.RH.Pareto.OrdinateCosine
