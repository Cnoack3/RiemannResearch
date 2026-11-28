import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ParetoOrdinateCosineCompleteness
import RiemannResearch.RH.ParetoOrdinatePairError
import RiemannResearch.RH.ParetoOrdinateCenteredFluctuations
import RiemannResearch.RH.ParetoOrdinateFiniteBands
import RiemannResearch.RH.IntegerDPPMellinObstruction
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ParetoWeights
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Quantitative centered fluctuations at actual positive zero ordinates

The fixed-frequency Landau limits diagonalize the unscaled cosine second
moment. Empirical centering removes physical site one. The parity estimate
and the choice of cutoff in the cubic lower bound follow the user-provided
argument. All finite-height sums retain the original zero multiplicities.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis.ActualZeroOrdinate
/-- Pareto mass times the physical coordinate at the positive integer `k+1`. -/
def rowCoefficient (v : ThresholdHilbert) (k : ℕ) : ℝ :=
  paretoWeight k * hilbertGibbsPhysical v k

private theorem coefficient_abs_sum (v : ThresholdHilbert) :
    Summable (fun k => |rowCoefficient v k|) := by
  simpa only [rowCoefficient, abs_mul, abs_of_pos (paretoWeight_pos _)] using
    hilbertGibbsPhysical_abs_summable v

private theorem coefficient_sq (v : ThresholdHilbert) (k : ℕ) :
    rowCoefficient v k ^ 2 = paretoWeight k * (v k)^2 := by
  rw [← hilbertGibbsPhysical_square v k]
  unfold rowCoefficient
  ring

private theorem coefficient_sq_sum (v : ThresholdHilbert) :
    Summable (fun k => rowCoefficient v k ^ 2) := by
  apply (hilbert_coordinate_square_summable v).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro k
  rw [coefficient_sq]
  have hw : paretoWeight k ≤ 1 := by
    rw [← paretoWeight_tsum]
    exact paretoWeight_hasSum.summable.le_tsum k (fun j _ => (paretoWeight_pos j).le)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg (v k))

private def freq (k : ℕ) : ℝ := Real.log ((k + 1 : ℕ) : ℝ)

private theorem row_hasSum (v : ThresholdHilbert) (t : ℝ) :
    HasSum (fun k => rowCoefficient v k * Real.cos (freq k * t))
      (inner ℝ (cosineRow t) v) := by
  have h : Summable (fun k => rowCoefficient v k * Real.cos (freq k * t)) := by
    apply (coefficient_abs_sum v).of_norm_bounded
    intro k
    simpa [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (freq k * t)) (abs_nonneg (rowCoefficient v k))
  convert h.hasSum using 1
  rw [hilbertGibbs_inner_physical]
  apply tsum_congr
  intro k
  have hc : hilbertGibbsPhysical (cosineRow t) k = Real.cos (freq k * t) := by
    change Real.sqrt (paretoWeight k) * _ / Real.sqrt (paretoWeight k) = _
    unfold freq
    field_simp [(Real.sqrt_pos.mpr (paretoWeight_pos k)).ne']
  rw [hc]
  unfold rowCoefficient
  ring

private theorem observation_abs_le (v : ThresholdHilbert) (t : ℝ) :
    |inner ℝ (cosineRow t) v| ≤ ‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (by
    simpa using mul_le_mul_of_nonneg_right (cosineRow_norm_le_one t) (norm_nonneg v))

private def sample (T : ℝ) (v : ThresholdHilbert) (i : Copies T) : ℝ :=
  inner ℝ (cosineRow (copyOrdinate T i)) v

private def centered (T : ℝ) (v : ThresholdHilbert) (i : Copies T) : ℝ :=
  sample T v i - rowObservationMean T v

private theorem sample_mean (T : ℝ) (v : ThresholdHilbert) :
    rowObservationMean T v = (∑ i, sample T v i) / (Ncount 0 T : ℝ) :=
  rowObservationMean_eq_average T v

/-- Exact finite-cutoff centering, with the repository's zero-count convention. -/
theorem rowObservationVariance_eq_second_sub (T : ℝ) (v : ThresholdHilbert) :
    rowObservationVariance T v =
      occurrenceAverage T (fun t => (inner ℝ (cosineRow t) v)^2) - rowObservationMean T v ^ 2 := by
  classical
  let m := rowObservationMean T v
  change (∑ i, (sample T v i - m)^2) / (Ncount 0 T : ℝ) =
    (∑ i, sample T v i ^ 2) / (Ncount 0 T : ℝ) - m^2
  by_cases hn : Ncount 0 T = 0
  · simp [m, sample_mean, hn]
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hn
  have hm : (∑ i, sample T v i) = m * (Ncount 0 T : ℝ) :=
    (eq_div_iff hN).mp (sample_mean T v) |>.symm
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, hm]
  field_simp [hN]
  ring

theorem rowObservationVariance_le_norm_sq (T : ℝ) (v : ThresholdHilbert) :
    rowObservationVariance T v ≤ ‖v‖^2 := by
  rw [rowObservationVariance_eq_second_sub]
  apply (sub_le_self _ (sq_nonneg _)).trans
  by_cases hn : Ncount 0 T = 0
  · simp [occurrenceAverage, hn]
  apply (div_le_iff₀ (show (0 : ℝ) < Ncount 0 T by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
  calc
    _ ≤ ∑ _i : Copies T, ‖v‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (observation_abs_le v (copyOrdinate T i)) 2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, mul_comm]

private theorem centered_sub (T : ℝ) (v w : ThresholdHilbert) (i : Copies T) :
    centered T (v-w) i = centered T v i - centered T w i := by
  simp only [centered, sample, rowObservationMean, inner_sub_right]
  ring

private theorem centered_add (T : ℝ) (v w : ThresholdHilbert) (i : Copies T) :
    centered T (v+w) i = centered T v i + centered T w i := by
  simp only [centered, sample, rowObservationMean, inner_add_right]
  ring

/-- Empirical centering is a contraction. The estimate is uniform in height. -/
theorem abs_rowObservationVariance_sub_le (T : ℝ) (v w : ThresholdHilbert) :
    |rowObservationVariance T v - rowObservationVariance T w| ≤ (‖v‖ + ‖w‖) * ‖v-w‖ := by
  classical
  let N : ℝ := Ncount 0 T
  have hv (z : ThresholdHilbert) : rowObservationVariance T z = (∑ i, centered T z i ^ 2) / N := rfl
  by_cases hn : N = 0
  · simp [hv, hn, mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]
  have hN : 0 < N := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hn)
  have hsum (z : ThresholdHilbert) : (∑ i, centered T z i ^ 2) ≤ ‖z‖^2 * N :=
    (div_le_iff₀ hN).mp (by simpa only [hv] using rowObservationVariance_le_norm_sq T z)
  have hdiff : (∑ i, centered T v i ^ 2) - (∑ i, centered T w i ^ 2) =
      ∑ i, centered T (v+w) i * centered T (v-w) i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [centered_add, centered_sub]
    ring
  rw [hv, hv, ← sub_div, hdiff, abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (centered T (v+w)) (centered T (v-w))
  have hb := mul_le_mul (hsum (v+w)) (hsum (v-w))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg (sq_nonneg _) hN.le)
  have h' : |∑ i, centered T (v+w) i * centered T (v-w) i| ≤ (‖v+w‖ * ‖v-w‖) * N := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    exact (hs.trans hb).trans_eq (by ring)
  exact h'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (norm_add_le v w) (norm_nonneg _)) hN.le)

private theorem recovery_pairing (T : ℝ) (v : ThresholdHilbert) (k : ℕ) :
    inner ℝ (recovery T k) v =
      (∑ i : Copies T, Real.cos (freq k * copyOrdinate T i) * sample T v i) / (Ncount 0 T : ℝ) := by
  rw [recovery, real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left, div_eq_inv_mul]
  rfl

private theorem recovery_pairing_bound (T : ℝ) (v : ThresholdHilbert) (k : ℕ) :
    |inner ℝ (recovery T k) v| ≤ ‖v‖ := by
  by_cases hn : Ncount 0 T = 0
  · simp [recovery_pairing, hn]
  rw [recovery_pairing, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Ncount 0 T from Nat.cast_nonneg _)]
  apply (div_le_iff₀ (show (0 : ℝ) < Ncount 0 T by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Copies T, ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
        (by simpa only [sample, one_mul] using observation_abs_le v (copyOrdinate T i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, mul_comm]

/-- The exact second moment at finite height uses each fixed-frequency Landau recovery. -/
theorem row_secondMoment_eq_series (T : ℝ) (v : ThresholdHilbert) :
    occurrenceAverage T (fun t => (inner ℝ (cosineRow t) v)^2) =
      ∑' k, rowCoefficient v k * inner ℝ (recovery T k) v := by
  classical
  let f (i : Copies T) (k : ℕ) :=
    (rowCoefficient v k * Real.cos (freq k * copyOrdinate T i)) * sample T v i
  have hf (i : Copies T) : HasSum (f i) (sample T v i ^ 2) := by
    simpa only [sq, f, sample] using (row_hasSum v (copyOrdinate T i)).mul_right (sample T v i)
  have hs : Summable (fun k => ∑ i, f i k) := summable_sum (fun i _ => (hf i).summable)
  calc
    _ = (∑ i, ∑' k, f i k) / (Ncount 0 T : ℝ) := by
      simp only [(hf _).tsum_eq, occurrenceAverage, sample]
    _ = (∑' k, ∑ i, f i k) * (Ncount 0 T : ℝ)⁻¹ := by
      rw [Summable.tsum_finsetSum (fun i _ => (hf i).summable), div_eq_mul_inv]
    _ = _ := by
      rw [← hs.tsum_mul_right]
      apply tsum_congr
      intro k
      simp only [f, recovery_pairing, div_eq_mul_inv, mul_assoc, ← Finset.mul_sum]

/-- Half the square energy of the nonconstant logarithmic frequencies. -/
def limitingRowVariance (v : ThresholdHilbert) : ℝ :=
  (∑' k : ℕ, rowCoefficient v (k+1)^2) / 2

/-- The empirical variance on all positive zero occurrences has the Haar cosine limit. -/
theorem rowObservationVariance_tendsto (v : ThresholdHilbert) :
    Tendsto (fun T => rowObservationVariance T v) atTop (𝓝 (limitingRowVariance v)) := by
  let g (k : ℕ) := diagonalMass k * rowCoefficient v k ^ 2
  have hg (k : ℕ) : Tendsto (fun T => rowCoefficient v k * inner ℝ (recovery T k) v)
      atTop (𝓝 (g k)) := by
    have h := ((recovery_tendsto k).inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))).const_mul
      (rowCoefficient v k)
    convert h using 1
    rw [real_inner_smul_left, real_inner_comm v (paretoPointHilbert k), inner_paretoPoint]
    congr 1
    unfold g rowCoefficient
    ring
  have hb (T : ℝ) (k : ℕ) : ‖rowCoefficient v k * inner ℝ (recovery T k) v‖ ≤
      |rowCoefficient v k| * ‖v‖ := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (recovery_pairing_bound T v k) (abs_nonneg _)
  have hsum := tendsto_tsum_of_dominated_convergence ((coefficient_abs_sum v).mul_right ‖v‖)
    hg (Eventually.of_forall hb)
  have hm : Tendsto (fun T => rowObservationMean T v) atTop (𝓝 (rowCoefficient v 0)) := by
    have h := first_recovery_tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
    simpa only [rowObservationMean, real_inner_comm v (paretoPointHilbert 0), inner_paretoPoint,
      rowCoefficient] using h
  have htail := (summable_nat_add_iff 1).mpr (coefficient_sq_sum v)
  have hgs : Summable g := (coefficient_sq_sum v).of_nonneg_of_le
    (fun k => mul_nonneg (by by_cases h : k = 0 <;> norm_num [diagonalMass, h]) (sq_nonneg _))
    (fun k => by
      dsimp [g]
      by_cases h : k = 0
      · simp [diagonalMass, h]
      · simp only [diagonalMass, if_neg h]
        nlinarith [sq_nonneg (rowCoefficient v k)])
  have h := hsum.sub (hm.pow 2)
  simp only [← row_secondMoment_eq_series, ← rowObservationVariance_eq_second_sub] at h
  convert h using 1
  congr 1
  have hzero : g 0 = rowCoefficient v 0 ^ 2 := by simp [g, diagonalMass]
  have hsucc (n : ℕ) : g (n+1) = (1 / 2 : ℝ) * rowCoefficient v (n+1)^2 := by
    simp [g, diagonalMass]
  rw [← hgs.sum_add_tsum_nat_add 1, Finset.sum_range_one, hzero]
  simp_rw [hsucc]
  rw [htail.tsum_mul_left]
  unfold limitingRowVariance
  ring

/-- The Parseval remainder of the finite projection tower bounds the variance error at every height.
-/
theorem finite_firstSiteVariance_error (T : ℝ) (n : ℕ) :
    let qn := (finiteSpace n)ᗮ.starProjection (paretoPointHilbert 0)
    |rowObservationVariance T qn - rowObservationVariance T firstSiteResidual| ≤
      (‖qn‖ + ‖firstSiteResidual‖) * Real.sqrt (‖qn‖^2 - ‖firstSiteResidual‖^2) := by
  let e := paretoPointHilbert 0
  let qn := (finiteSpace n)ᗮ.starProjection e
  have h := RiemannResearch.Analysis.ExhaustiveWalk.walkError_eq_limitingError_add
    residueAtom id e n
  have hd : ‖qn - firstSiteResidual‖^2 = ‖qn‖^2 - ‖firstSiteResidual‖^2 := by
    change ‖e - (finiteSpace n).starProjection e‖^2 =
      ‖e - closedSpace.starProjection e‖^2 +
        ‖closedSpace.starProjection e - (finiteSpace n).starProjection e‖^2 at h
    simp only [qn, firstSiteResidual, Submodule.starProjection_orthogonal_val]
    change ‖(e - (finiteSpace n).starProjection e) - (e - closedSpace.starProjection e)‖^2 = _
    rw [sub_sub_sub_cancel_left]
    linarith only [h]
  change _ ≤ (‖qn‖ + ‖firstSiteResidual‖) * Real.sqrt (‖qn‖^2 - ‖firstSiteResidual‖^2)
  rw [← hd, Real.sqrt_sq (norm_nonneg _)]
  exact abs_rowObservationVariance_sub_le T qn firstSiteResidual

/-- Any cofinal finite legal ranks give the same variance limit at growing heights. -/
theorem finite_firstSiteVariance_tendsto {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    Tendsto (fun T => rowObservationVariance T
      ((finiteSpace (rank T))ᗮ.starProjection (paretoPointHilbert 0))) atTop
      (𝓝 (limitingRowVariance firstSiteResidual)) := by
  let Q (T : ℝ) := (finiteSpace (rank T))ᗮ.starProjection (paretoPointHilbert 0)
  have hQ : Tendsto Q atTop (𝓝 firstSiteResidual) := moving_residual_tendsto tendsto_const_nhds hr
  have he := (hQ.norm.add_const ‖firstSiteResidual‖).mul
    (tendsto_iff_norm_sub_tendsto_zero.mp hQ)
  rw [mul_zero] at he
  have hd := squeeze_zero (fun T => abs_nonneg (rowObservationVariance T (Q T) -
      rowObservationVariance T firstSiteResidual))
    (fun T => abs_rowObservationVariance_sub_le T (Q T) firstSiteResidual) he
  have hd' := tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa only [sub_zero, Real.norm_eq_abs] using hd :
      Tendsto (fun T => ‖(rowObservationVariance T (Q T) -
        rowObservationVariance T firstSiteResidual) - 0‖)
        atTop (𝓝 0))
  simpa only [zero_add, sub_add_cancel] using
    hd'.add (rowObservationVariance_tendsto firstSiteResidual)

private theorem tail_sum_le {f : ℕ → ℝ} (hf : Summable f) (hp : ∀ k, 0 ≤ f k) (M : ℕ) :
    (∑' k, f (k+M)) ≤ ∑' k, f k := by
  rw [← hf.sum_add_tsum_nat_add M]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => hp k)

/-- Cauchy–Schwarz on the exact Pareto tail starting at physical site M+1. -/
theorem rowCoefficient_tail_le (v : ThresholdHilbert) (M : ℕ) :
    (∑' k, |rowCoefficient v (k+M)|) ≤ Real.sqrt (‖v‖^2 / ((M : ℝ)+1)) := by
  have hw := paretoWeight_hasSum.summable
  have hm : (∑' k, paretoWeight (k+M)) = 1 / ((M : ℝ)+1) := by
    have h := hw.sum_add_tsum_nat_add M
    rw [paretoWeight_partial_sum, paretoWeight_tsum] at h
    linarith
  have hW := (summable_nat_add_iff M).mpr hw
  have hV := (summable_nat_add_iff M).mpr (hilbert_coordinate_square_summable v)
  have htail := tail_sum_le (hilbert_coordinate_square_summable v) (fun _ => sq_nonneg _) M
  rw [← hilbert_norm_sq] at htail
  have hcoeff (k : ℕ) : |rowCoefficient v k| = Real.sqrt (paretoWeight k) * |v k| := by
    apply (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, mul_pow, sq_abs, Real.sq_sqrt (paretoWeight_pos k).le, coefficient_sq]
  have hA := (summable_nat_add_iff M).mpr (coefficient_abs_sum v)
  apply le_of_tendsto' hA.hasSum.tendsto_sum_nat
  intro L
  apply (Real.le_sqrt (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mpr
  simp_rw [hcoeff]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L)
    (fun k => Real.sqrt (paretoWeight (k+M))) (fun k => |v (k+M)|)
  simp only [Real.sq_sqrt (paretoWeight_pos _).le, sq_abs] at h
  have h₁ := hW.sum_le_tsum (Finset.range L) (fun k _ => (paretoWeight_pos (k+M)).le)
  have h₂ := hV.sum_le_tsum (Finset.range L) (fun k _ => sq_nonneg (v (k+M)))
  rw [hm] at h₁
  exact h.trans ((mul_le_mul h₁ (h₂.trans htail)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)).trans_eq (by ring))

/-- Finite frequency head for the actual centered variance. The error is uniform in height
and applies to every finite legal projection residual. -/
theorem abs_variance_sub_recovery_head_le (T : ℝ) (v : ThresholdHilbert) (M : ℕ) :
    |rowObservationVariance T v -
      ((∑ k ∈ Finset.range M, rowCoefficient v k * inner ℝ (recovery T k) v) -
        rowObservationMean T v ^ 2)| ≤ Real.sqrt (‖v‖^2 / ((M : ℝ)+1)) * ‖v‖ := by
  let f (k : ℕ) := rowCoefficient v k * inner ℝ (recovery T k) v
  have hb (k : ℕ) : ‖f k‖ ≤ |rowCoefficient v k| * ‖v‖ := by
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (recovery_pairing_bound T v k) (abs_nonneg _)
  have hf := ((coefficient_abs_sum v).mul_right ‖v‖).of_norm_bounded hb
  have hs := (summable_nat_add_iff M).mpr hf
  have ha := (summable_nat_add_iff M).mpr (coefficient_abs_sum v)
  rw [rowObservationVariance_eq_second_sub, row_secondMoment_eq_series, sub_sub_sub_cancel_right]
  change |(∑' k, f k) - (∑ k ∈ Finset.range M, f k)| ≤ _
  rw [← hf.sum_add_tsum_nat_add M, add_sub_cancel_left]
  calc
    _ ≤ ∑' k, ‖f (k+M)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k, |rowCoefficient v (k+M)| * ‖v‖ :=
      hs.norm.tsum_le_tsum (fun k => hb (k+M)) (ha.mul_right _)
    _ ≤ _ := by
      rw [ha.tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (rowCoefficient_tail_le v M) (norm_nonneg _)

/-- The cosine polynomial from the first M physical sites. -/
def cosineSiteHead (v : ThresholdHilbert) (M : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range M, rowCoefficient v k * Real.cos (freq k * t)

private theorem head_abs_le (v : ThresholdHilbert) (M : ℕ) (t : ℝ) :
    |cosineSiteHead v M t| ≤ ‖v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb (k : ℕ) : |rowCoefficient v k * Real.cos (freq k * t)| ≤ |rowCoefficient v k| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg (rowCoefficient v k))
  have hw := (coefficient_abs_sum v).sum_le_tsum (Finset.range M) (fun _ _ => abs_nonneg _)
  apply (Finset.sum_le_sum (fun k _ => hb k)).trans (hw.trans _)
  simpa using rowCoefficient_tail_le v 0

private theorem observation_sub_head (v : ThresholdHilbert) (M : ℕ) (t : ℝ) :
    |inner ℝ (cosineRow t) v - cosineSiteHead v M t| ≤ Real.sqrt (‖v‖^2 / ((M : ℝ)+1)) := by
  let f (k : ℕ) := rowCoefficient v k * Real.cos (freq k * t)
  have h : HasSum f (inner ℝ (cosineRow t) v) := row_hasSum v t
  have hsplit := h.summable.sum_add_tsum_nat_add M
  rw [h.tsum_eq] at hsplit
  change |inner ℝ (cosineRow t) v - ∑ k ∈ Finset.range M, f k| ≤ _
  rw [← hsplit, add_sub_cancel_left]
  have hs := (summable_nat_add_iff M).mpr h.summable
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  apply le_trans _ (rowCoefficient_tail_le v M)
  apply hs.norm.tsum_le_tsum _ ((summable_nat_add_iff M).mpr (coefficient_abs_sum v))
  intro k
  dsimp only [f]
  rw [Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
    (abs_nonneg (rowCoefficient v (k+M)))

private theorem avg_abs_le {f : ℝ → ℝ} {b : ℝ} (T : ℝ) (hb : 0 ≤ b)
    (h : ∀ t, |f t| ≤ b) : |occurrenceAverage T f| ≤ b := by
  by_cases hn : Ncount 0 T = 0
  · simpa only [occurrenceAverage, hn, Nat.cast_zero, div_zero, abs_zero] using hb
  rw [occurrenceAverage, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Ncount 0 T from Nat.cast_nonneg _)]
  apply (div_le_iff₀ (show (0 : ℝ) < Ncount 0 T by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Copies T, b := Finset.sum_le_sum (fun i _ => h (copyOrdinate T i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, mul_comm]

private theorem avg_sub (T : ℝ) (f g : ℝ → ℝ) :
    occurrenceAverage T f - occurrenceAverage T g = occurrenceAverage T (fun t => f t - g t) := by
  simp only [occurrenceAverage, Finset.sum_sub_distrib, sub_div]

private theorem sq_diff_bound {x y b e : ℝ} (hx : |x| ≤ b) (hy : |y| ≤ b)
    (hd : |x - y| ≤ e) : |x^2 - y^2| ≤ (b+b)*e := by
  rw [show x^2-y^2 = (x+y)*(x-y) by ring, abs_mul]
  exact mul_le_mul ((abs_add_le x y).trans (add_le_add hx hy)) hd (abs_nonneg _)
    (add_nonneg ((abs_nonneg _).trans hx) ((abs_nonneg _).trans hy))

/-- Both the mean and the second moment can be computed on a finite physical Fourier head.
The bound is uniform over heights, with the legal rank entering only through the vector norm. -/
theorem abs_variance_sub_cosineSiteHead_le (T : ℝ) (v : ThresholdHilbert) (M : ℕ) :
    |rowObservationVariance T v -
      (occurrenceAverage T (fun t => cosineSiteHead v M t ^ 2) -
        occurrenceAverage T (cosineSiteHead v M)^2)| ≤
      4 * ‖v‖ * Real.sqrt (‖v‖^2 / ((M : ℝ)+1)) := by
  let f (t : ℝ) := inner ℝ (cosineRow t) v
  let g := cosineSiteHead v M
  let e := Real.sqrt (‖v‖^2 / ((M : ℝ)+1))
  have hd : |occurrenceAverage T f - occurrenceAverage T g| ≤ e := by
    rw [avg_sub]
    exact avg_abs_le T (Real.sqrt_nonneg _) (observation_sub_head v M)
  have hm := sq_diff_bound (avg_abs_le T (norm_nonneg v) (observation_abs_le v))
    (avg_abs_le T (norm_nonneg v) (head_abs_le v M)) hd
  have hs : |occurrenceAverage T (fun t => f t^2) - occurrenceAverage T (fun t => g t^2)| ≤
      (‖v‖+‖v‖)*e := by
    rw [avg_sub]
    apply avg_abs_le T (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.sqrt_nonneg _))
    intro t
    exact sq_diff_bound (observation_abs_le v t) (head_abs_le v M t) (observation_sub_head v M t)
  rw [rowObservationVariance_eq_second_sub, rowObservationMean_eq_average]
  change |(_ - occurrenceAverage T f ^ 2) - (_ - occurrenceAverage T g ^ 2)| ≤ 4*‖v‖*e
  rw [sub_sub_sub_comm]
  exact (abs_sub _ _).trans ((add_le_add hs hm).trans_eq (by ring))

/-- The real part of the normalized empirical ordinate Fourier transform. -/
def occurrenceCosineTrace (T u : ℝ) : ℝ :=
  occurrenceAverage T (fun t => Real.cos (u*t))

theorem occurrenceCosineTrace_eq_ordinateSum (T u : ℝ) :
    occurrenceCosineTrace T u = (ordinateSum T u / (Ncount 0 T : ℂ)).re := by
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, ordinateSum, sum_eq_copies, Complex.re_sum]
  simp only [occurrenceCosineTrace, occurrenceAverage, copyOrdinate,
    RiemannResearch.Analysis.ZeroOrdinate.phase, Complex.exp_ofReal_mul_I_re]

private theorem avg_weighted_sum (T : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (f : ℕ → ℝ → ℝ) :
    occurrenceAverage T (fun t => ∑ k ∈ s, a k * f k t) =
      ∑ k ∈ s, a k * occurrenceAverage T (f k) := by
  unfold occurrenceAverage
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  ring

private theorem avg_cos_product (T u v : ℝ) :
    occurrenceAverage T (fun t => Real.cos (u*t) * Real.cos (v*t)) =
      (occurrenceCosineTrace T (u-v) + occurrenceCosineTrace T (u+v)) / 2 := by
  have hp (t : ℝ) : Real.cos (u*t) * Real.cos (v*t) =
      (Real.cos ((u-v)*t) + Real.cos ((u+v)*t)) / 2 := by
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp only [occurrenceCosineTrace, occurrenceAverage, hp, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- The finite physical polynomial uses only the sum and difference log frequencies
and the single-frequency means of the actual zero occurrences. -/
theorem cosineSiteHead_variance_eq_traces (T : ℝ) (v : ThresholdHilbert) (M : ℕ) :
    let u (k : ℕ) := Real.log ((k+1 : ℕ) : ℝ)
    occurrenceAverage T (fun t => cosineSiteHead v M t ^ 2) -
        occurrenceAverage T (cosineSiteHead v M)^2 =
      (∑ i ∈ Finset.range M, rowCoefficient v i * ∑ j ∈ Finset.range M, rowCoefficient v j *
        ((occurrenceCosineTrace T (u i - u j) + occurrenceCosineTrace T (u i + u j))/2)) -
      (∑ i ∈ Finset.range M, rowCoefficient v i * occurrenceCosineTrace T (u i))^2 := by
  let a := rowCoefficient v
  let c (k : ℕ) (t : ℝ) := Real.cos (freq k * t)
  let S := Finset.range M
  have h (t : ℝ) : cosineSiteHead v M t ^ 2 =
      ∑ i ∈ S, a i * ∑ j ∈ S, a j * (c i t * c j t) := by
    change (∑ i ∈ S, a i * c i t)^2 = _
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmean : occurrenceAverage T (cosineSiteHead v M) =
      ∑ i ∈ S, a i * occurrenceCosineTrace T (freq i) := avg_weighted_sum T S a c
  simp_rw [h]
  rw [hmean, avg_weighted_sum]
  simp_rw [avg_weighted_sum, c, avg_cos_product]
  rfl

theorem limitingRowVariance_le (v : ThresholdHilbert) :
    limitingRowVariance v ≤ ‖v‖^2 / 12 := by
  have hW (k : ℕ) : paretoWeight (k+1) ≤ 1/6 := by
    unfold paretoWeight
    push_cast
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k : ℝ)]
  have hsum := (summable_nat_add_iff 1).mpr (coefficient_sq_sum v)
  have hV := (summable_nat_add_iff 1).mpr (hilbert_coordinate_square_summable v)
  have h := hsum.tsum_le_tsum (fun k => by
    rw [coefficient_sq]
    exact mul_le_mul_of_nonneg_right (hW k) (sq_nonneg (v (k+1)))) (hV.mul_left (1/6))
  rw [hV.tsum_mul_left] at h
  have he := tail_sum_le (hilbert_coordinate_square_summable v) (fun _ => sq_nonneg _) 1
  rw [← hilbert_norm_sq] at he
  unfold limitingRowVariance
  linarith

theorem firstSiteResidual_first_coefficient :
    rowCoefficient firstSiteResidual 0 = ‖firstSiteResidual‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  change rowCoefficient firstSiteResidual 0 =
    inner ℝ (closedSpaceᗮ.starProjection (paretoPointHilbert 0)) firstSiteResidual
  have hfix : closedSpaceᗮ.starProjection firstSiteResidual = firstSiteResidual :=
    Submodule.starProjection_eq_self_iff.mpr (closedSpaceᗮ.starProjection_apply_mem _)
  rw [closedSpaceᗮ.inner_starProjection_left_eq_right, hfix, real_inner_comm, inner_paretoPoint]
  rfl

/-- The signed coefficient on odd physical sites, extended by zero to even sites. -/
def oddCoefficient (k : ℕ) : ℝ :=
  if (k+1)%2 = 1 then rowCoefficient firstSiteResidual k else 0

private theorem odd_abs_le (k : ℕ) : |oddCoefficient k| ≤ |rowCoefficient firstSiteResidual k| := by
  unfold oddCoefficient
  split <;> simp

private theorem odd_sum : Summable oddCoefficient :=
  (coefficient_abs_sum firstSiteResidual).of_norm_bounded (fun k => by
    simpa only [Real.norm_eq_abs] using odd_abs_le k)

/-- Signed parity cancellation, with the physical first site removed. -/
theorem firstSiteResidual_odd_tail :
    (∑' k, oddCoefficient (k+1)) = -‖firstSiteResidual‖^2 := by
  have hmem := RiemannResearch.Analysis.ProjectionCorrelationCompleteness.atom_mem_dictionaryClosure
    residueAtom 0
  have ho := (closedSpace.mem_orthogonal firstSiteResidual).mp
    (closedSpaceᗮ.starProjection_apply_mem _) (residueAtom 0) hmem
  rw [hilbertGibbs_inner_physical] at ho
  have hterm (k : ℕ) : paretoWeight k * (hilbertGibbsPhysical (residueAtom 0) k *
      hilbertGibbsPhysical firstSiteResidual k) = oddCoefficient k * (1/2) := by
    rw [hilbertGibbsPhysical_eq, residueAtom, normalizedResidueHilbert_sequence]
    have h : (k+1)%2 = 0 ∨ (k+1)%2 = 1 := by omega
    rcases h with h | h
    · simp [ArithmeticCumulative.residueFraction, oddCoefficient, h]
    · simp [ArithmeticCumulative.residueFraction, oddCoefficient, rowCoefficient, h]
      ring
  simp_rw [hterm] at ho
  rw [odd_sum.tsum_mul_right] at ho
  have hsplit := odd_sum.sum_add_tsum_nat_add 1
  have hzero : oddCoefficient 0 = ‖firstSiteResidual‖^2 := firstSiteResidual_first_coefficient
  rw [Finset.sum_range_one, hzero] at hsplit
  linarith

/-- Parity forces a cubic amount of nonconstant frequency energy. Source: user-provided argument. -/
theorem firstSiteResidual_cubic_le :
    (‖firstSiteResidual‖^2)^3 / 32 ≤ limitingRowVariance firstSiteResidual := by
  let v := firstSiteResidual
  let δ := ‖v‖^2
  let S := ∑' k : ℕ, rowCoefficient v (k+1)^2
  change δ^3 / 32 ≤ S / 2
  have hδ : 0 ≤ δ := sq_nonneg _
  have hS : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  rcases hδ.eq_or_lt with h | hpos
  · rw [← h]
    linarith
  let M := ⌊4/δ⌋₊
  have hM : (M : ℝ) * δ ≤ 4 := (le_div_iff₀ hpos).mp (Nat.floor_le (by positivity))
  have hM' : 4 < ((M : ℝ)+1)*δ := (div_lt_iff₀ hpos).mp (Nat.lt_floor_add_one _)
  let B := ∑ k ∈ Finset.range M, oddCoefficient (k+1)
  let R := ∑' k : ℕ, oddCoefficient ((k+M)+1)
  have hBR : B + R = -δ := ((summable_nat_add_iff 1).mpr odd_sum).sum_add_tsum_nat_add M
    |>.trans firstSiteResidual_odd_tail
  have hR : |R| ≤ δ/2 := by
    have ha := (summable_nat_add_iff (M+1)).mpr odd_sum.abs
    have hb := (summable_nat_add_iff (M+1)).mpr (coefficient_abs_sum v)
    have hr : |R| ≤ ∑' k, |oddCoefficient (k+(M+1))| := by
      simpa only [R, Nat.add_assoc, Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (show Summable (fun k => ‖oddCoefficient (k+(M+1))‖) from ha)
    apply hr.trans
    apply (ha.tsum_le_tsum (fun k => odd_abs_le (k+(M+1))) hb).trans
    apply (rowCoefficient_tail_le v (M+1)).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    change δ / (((M+1 : ℕ) : ℝ)+1) ≤ _
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hM'.le hpos.le, sq_nonneg δ]
  have hB : δ/2 ≤ |B| := by
    have h := abs_add_le B R
    rw [hBR, abs_neg, abs_of_nonneg hpos.le] at h
    linarith
  have hBS : B^2 ≤ (M : ℝ)*S := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M) (fun _ => (1 : ℝ))
      (fun k => oddCoefficient (k+1))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hs := (summable_nat_add_iff 1).mpr (coefficient_sq_sum v)
    apply le_trans _ (hs.sum_le_tsum (Finset.range M) (fun _ _ => sq_nonneg _))
    apply Finset.sum_le_sum
    intro k _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (odd_abs_le (k+1)) 2
  have hh := pow_le_pow_left₀ (show 0 ≤ δ/2 by positivity) hB 2
  rw [sq_abs] at hh
  nlinarith only [mul_le_mul_of_nonneg_right (hh.trans hBS) hpos.le,
    mul_le_mul_of_nonneg_right hM hS]

/-- Each right-hand zero gives an explicit floor for the unnormalized physical probe. -/
theorem rightZero_variance_floor (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (((2*s.re-1) * ‖1 - (2 : ℂ)^(-s)‖^2 / ‖s‖^2)^3) / 32 ≤
      limitingRowVariance firstSiteResidual := by
  have hf := IntegerDPP.mellinVacancyFloor_le_limitingVacancy s hs hs1 hz
  rw [IntegerDPP.limitingVacancy_eq_kernel_complement, IntegerDPP.mellinVacancyFloor_eq s hs] at hf
  have hδ : ((2*s.re-1) * ‖1 - (2 : ℂ)^(-s)‖^2 / ‖s‖^2) ≤ ‖firstSiteResidual‖^2 := by
    rw [firstSiteResidual, first_site_residual_sq]
    calc
      _ = (2 * (2*s.re-1) * ‖1 - (2 : ℂ)^(-s)‖^2 / ‖s‖^2) / 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hf (by norm_num)
  apply le_trans _ firstSiteResidual_cubic_le
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact pow_le_pow_left₀ (div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)) hδ 3

/-- A cofinal variance upper bound of zero is exactly the remaining arithmetic estimate. -/
theorem rh_iff_finite_firstSiteVariance {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    RiemannHypothesis ↔
      liminf (fun T => rowObservationVariance T
        ((finiteSpace (rank T))ᗮ.starProjection (paretoPointHilbert 0))) atTop ≤ 0 := by
  rw [(finite_firstSiteVariance_tendsto hr).liminf_eq, rh_iff_first_site_vacancy_zero,
    ← first_site_residual_sq]
  change ‖firstSiteResidual‖^2 = 0 ↔ limitingRowVariance firstSiteResidual ≤ 0
  constructor
  · intro h
    simpa only [h, zero_div] using limitingRowVariance_le firstSiteResidual
  · intro h
    have hc := firstSiteResidual_cubic_le.trans h
    by_contra hn
    have hp : 0 < ‖firstSiteResidual‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
    exact (not_lt_of_ge hc) (by positivity)

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_finite_firstSiteVariance' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_finite_firstSiteVariance

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rightZero_variance_floor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightZero_variance_floor

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.abs_variance_sub_cosineSiteHead_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abs_variance_sub_cosineSiteHead_le

end RiemannResearch.RH.Pareto.OrdinateCosine
