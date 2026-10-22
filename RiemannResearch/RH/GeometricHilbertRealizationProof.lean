import RiemannResearch.RH.GeometricHilbertRealizationResearchTargets
import RiemannResearch.RH.ParetoGibbsHilbertEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Full concrete geometric L2 realization, with the actual integral adjoint.
Proves the exact research target for all of ThresholdHilbert, including
almost-everywhere realization, contraction, the coordinate integral adjoint,
and adjoint composition equal to the Gibbs operator.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

private theorem latent_ae_mem : ∀ᵐ t ∂geometricLatentMeasure, t ∈ Set.Ioo (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ioo

private theorem latent_eq_Ioc :
    geometricLatentMeasure = volume.restrict (Set.Ioc (0 : ℝ) 1) :=
  restrict_Ioo_eq_restrict_Ioc

private theorem probability_continuous (n : ℕ) : Continuous (geometricProbability n) :=
  (continuous_const.sub continuous_id).mul (continuous_id.pow n)

private theorem probability_integrable (n : ℕ) :
    Integrable (geometricProbability n) geometricLatentMeasure := by
  rw [latent_eq_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    ((probability_continuous n).intervalIntegrable 0 1)

/-- Every fixed conditional geometric law is dominated by a finite multiple of
the Pareto law. The constant depends on the latent parameter. -/
private theorem probability_pareto_ratio_summable {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    Summable (fun n => geometricProbability n t / paretoWeight n) := by
  have htnorm : ‖t‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
  have h0 := (hasSum_geometric_of_norm_lt_one htnorm).summable
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one htnorm).summable
  have h2 : Summable (fun n : ℕ => (n : ℝ)^2*t^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 htnorm
  convert! ((h2.add (h1.mul_left 3)).add (h0.mul_left 2)).mul_left (1-t) using 1
  funext n
  change (1-t)*t^n / (1 / (((n : ℝ)+1)*((n : ℝ)+2))) =
    (1-t)*(((n : ℝ)^2*t^n + 3*((n : ℝ)*t^n)) + 2*t^n)
  field_simp
  <;> ring

theorem geometricTransform_norm_summable_of_weighted {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    Summable (fun n => ‖f n * geometricProbability n t‖) := by
  let C : ℝ := ∑' n, geometricProbability n t / paretoWeight n
  have hp (n : ℕ) : 0 ≤ geometricProbability n t :=
    geometricProbability_nonneg n ⟨ht.1.le,ht.2.le⟩
  have hb (n : ℕ) : geometricProbability n t ≤ C * paretoWeight n := by
    apply (div_le_iff₀ (paretoWeight_pos n)).mp
    exact (probability_pareto_ratio_summable ht).le_tsum n
      (fun j _ => div_nonneg (hp j) (paretoWeight_pos j).le)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) (hf.mul_left C)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp n)]
  have h := mul_le_mul_of_nonneg_left (hb n) (abs_nonneg (f n))
  nlinarith [h]

private theorem geometricTransform_aestronglyMeasurable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    AEStronglyMeasurable (geometricTransform f) geometricLatentMeasure := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
    (f := fun N t => ∑ n ∈ Finset.range N, f n * geometricProbability n t)
  · intro N
    exact (continuous_finsetSum _ (fun n _ =>
      continuous_const.mul (probability_continuous n))).aestronglyMeasurable
  · filter_upwards [latent_ae_mem] with t ht
    exact (geometricTransform_norm_summable_of_weighted hf ht).of_norm.hasSum.tendsto_sum_nat

/-- An integrable norm majorant for an absolutely integrable series. -/
private theorem integrable_norm_tsum_of_summable_integral
    {F : ℕ → ℝ → ℝ} (hF : ∀ n, Integrable (F n) geometricLatentMeasure)
    (hI : Summable (fun n => ∫ t, ‖F n t‖ ∂geometricLatentMeasure)) :
    Integrable (fun t => ∑' n, ‖F n t‖) geometricLatentMeasure := by
  by_contra hnot
  have hswap := integral_tsum_of_summable_integral_norm (fun n => (hF n).norm)
    (by simpa only [norm_norm] using hI)
  have hzero : (∑' n, ∫ t, ‖F n t‖ ∂geometricLatentMeasure) = 0 := by
    rw [hswap, integral_undef hnot]
  have heach (n : ℕ) : ∀ᵐ t ∂geometricLatentMeasure, ‖F n t‖ = 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun t => norm_nonneg _) (hF n).norm).mp
    have hle := hI.le_tsum n (fun j _ => integral_nonneg (fun t => norm_nonneg _))
    rw [hzero] at hle
    exact le_antisymm hle (integral_nonneg (fun t => norm_nonneg _))
  have hae : (fun t => ∑' n, ‖F n t‖) =ᵐ[geometricLatentMeasure] fun _ => 0 := by
    filter_upwards [ae_all_iff.mpr heach] with t ht
    simp only [ht, tsum_zero]
  exact hnot ((integrable_zero ℝ ℝ geometricLatentMeasure : Integrable (fun _ : ℝ => (0 : ℝ))
    geometricLatentMeasure).congr hae.symm)

theorem geometricTransform_integrable_of_weighted {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    Integrable (geometricTransform f) geometricLatentMeasure := by
  have hi (n : ℕ) : Integrable (fun t => f n * geometricProbability n t)
      geometricLatentMeasure := (probability_integrable n).const_mul _
  have hn : Summable (fun n => ∫ t, ‖f n * geometricProbability n t‖
      ∂geometricLatentMeasure) := by
    simp only [latent_eq_Ioc, geometricTransform_term_integral_norm]
    exact hf.congr (fun n => mul_comm _ _)
  apply (integrable_norm_tsum_of_summable_integral hi hn).mono'
    (geometricTransform_aestronglyMeasurable hf)
  filter_upwards [latent_ae_mem] with t ht
  exact norm_tsum_le_tsum_norm (geometricTransform_norm_summable_of_weighted hf ht)

private theorem geometricTransform_latent_integral {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    (∫ t, geometricTransform f t ∂geometricLatentMeasure) =
      ∑' n, paretoWeight n * f n := by
  rw [latent_eq_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact geometricTransform_integral_of_summable f (hf.congr (fun n => mul_comm _ _))

private theorem geometricTransform_sq_le {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * (f n)^2)) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    (geometricTransform f t)^2 ≤ geometricTransform (fun n => (f n)^2) t := by
  have hf1 := pareto_abs_summable_of_square hf
  have hf2 : Summable (fun n => paretoWeight n * |(f n)^2|) := by
    simpa only [abs_sq] using hf
  have hs1 := (geometricTransform_norm_summable_of_weighted hf1 ht).of_norm
  have hs2 := (geometricTransform_norm_summable_of_weighted hf2 ht).of_norm
  have hp := geometricProbability_hasSum ⟨ht.1.le,ht.2⟩
  let m := geometricTransform f t
  have hvar : (∑' n, geometricProbability n t * (f n-m)^2) =
      geometricTransform (fun n => (f n)^2) t - m^2 := by
    have he (n : ℕ) : geometricProbability n t * (f n-m)^2 =
        ((f n)^2*geometricProbability n t + m^2*geometricProbability n t) -
          (2*m)*(f n*geometricProbability n t) := by ring
    simp_rw [he]
    rw [(hs2.add (hp.summable.mul_left (m^2))).tsum_sub (hs1.mul_left (2*m)),
      hs2.tsum_add (hp.summable.mul_left (m^2)), tsum_mul_left, tsum_mul_left, hp.tsum_eq]
    change geometricTransform (fun n => (f n)^2) t + m^2*1 - (2*m)*m = _
    ring
  have hn : 0 ≤ ∑' n, geometricProbability n t * (f n-m)^2 :=
    tsum_nonneg (fun n => mul_nonneg
      (geometricProbability_nonneg n ⟨ht.1.le,ht.2.le⟩) (sq_nonneg _))
  rw [hvar] at hn
  linarith

theorem geometricTransform_memLp_of_square {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * (f n)^2)) :
    MemLp (geometricTransform f) 2 geometricLatentMeasure := by
  have hf1 := pareto_abs_summable_of_square hf
  have hf2 : Summable (fun n => paretoWeight n * |(f n)^2|) := by
    simpa only [abs_sq] using hf
  have hm := geometricTransform_aestronglyMeasurable hf1
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (geometricTransform_integrable_of_weighted hf2).mono' (hm.pow 2)
  filter_upwards [latent_ae_mem] with t ht
  change ‖(geometricTransform f t)^2‖ ≤ geometricTransform (fun n => (f n)^2) t
  rw [Real.norm_eq_abs, abs_sq]
  exact geometricTransform_sq_le hf ht

theorem geometricTransform_sq_integral_le_full {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * (f n)^2)) :
    (∫ t, (geometricTransform f t)^2 ∂geometricLatentMeasure) ≤
      ∑' n, paretoWeight n * (f n)^2 := by
  have hf2 : Summable (fun n => paretoWeight n * |(f n)^2|) := by
    simpa only [abs_sq] using hf
  rw [← geometricTransform_latent_integral hf2]
  apply integral_mono_ae (geometricTransform_memLp_of_square hf).integrable_sq
    (geometricTransform_integrable_of_weighted hf2)
  filter_upwards [latent_ae_mem] with t ht
  exact geometricTransform_sq_le hf ht

def geometricHilbertLift (f : ThresholdHilbert) : GeometricLatentL2 :=
  (geometricTransform_memLp_of_square (hilbertGibbsPhysical_square_summable f)).toLp
    (geometricTransform (hilbertGibbsPhysical f))

theorem geometricHilbertLift_ae (f : ThresholdHilbert) :
    ∀ᵐ t ∂geometricLatentMeasure,
      geometricHilbertLift f t = geometricTransform (hilbertGibbsPhysical f) t :=
  (geometricTransform_memLp_of_square (hilbertGibbsPhysical_square_summable f)).coeFn_toLp

private theorem geometricHilbertLift_norm_sq (f : ThresholdHilbert) :
    ‖geometricHilbertLift f‖^2 =
      ∫ t, (geometricTransform (hilbertGibbsPhysical f) t)^2 ∂geometricLatentMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [geometricHilbertLift_ae f] with t ht
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, ht]

theorem geometricHilbertLift_norm_le (f : ThresholdHilbert) :
    ‖geometricHilbertLift f‖ ≤ ‖f‖ := by
  have h := geometricTransform_sq_integral_le_full (hilbertGibbsPhysical_square_summable f)
  rw [← geometricHilbertLift_norm_sq, hilbertGibbsPhysical_norm_sq] at h
  nlinarith [norm_nonneg (geometricHilbertLift f), norm_nonneg f]

private theorem geometricTransform_add_full (f g : ThresholdHilbert) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    geometricTransform (hilbertGibbsPhysical (f+g)) t =
      geometricTransform (hilbertGibbsPhysical f) t +
        geometricTransform (hilbertGibbsPhysical g) t := by
  rw [hilbertGibbsPhysical_add]
  simp only [geometricTransform, add_mul]
  exact ((geometricTransform_norm_summable_of_weighted (hilbertGibbsPhysical_abs_summable f)
    ht).of_norm).tsum_add
      (geometricTransform_norm_summable_of_weighted (hilbertGibbsPhysical_abs_summable g)
        ht).of_norm

private theorem geometricTransform_smul_full (c : ℝ) (f : ThresholdHilbert) (t : ℝ) :
    geometricTransform (hilbertGibbsPhysical (c • f)) t =
      c * geometricTransform (hilbertGibbsPhysical f) t := by
  rw [hilbertGibbsPhysical_smul]
  simp only [geometricTransform, mul_assoc, tsum_mul_left]

def geometricHilbertLinear : ThresholdHilbert →ₗ[ℝ] GeometricLatentL2 where
  toFun := geometricHilbertLift
  map_add' f g := by
    apply Lp.ext
    filter_upwards [geometricHilbertLift_ae (f+g), geometricHilbertLift_ae f,
      geometricHilbertLift_ae g, Lp.coeFn_add (geometricHilbertLift f) (geometricHilbertLift g),
      latent_ae_mem] with t hfg hf hg hadd ht
    rw [hadd, hfg]
    change geometricTransform (hilbertGibbsPhysical (f+g)) t =
      geometricHilbertLift f t + geometricHilbertLift g t
    rw [hf,hg]
    exact geometricTransform_add_full f g ht
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [geometricHilbertLift_ae (c • f), geometricHilbertLift_ae f,
      Lp.coeFn_smul c (geometricHilbertLift f)] with t hcf hf hsmul
    change geometricHilbertLift (c • f) t = (c • geometricHilbertLift f) t
    rw [hsmul,hcf]
    change geometricTransform (hilbertGibbsPhysical (c • f)) t = c * geometricHilbertLift f t
    rw [hf]
    exact geometricTransform_smul_full c f t

def geometricHilbertContinuous : ThresholdHilbert →L[ℝ] GeometricLatentL2 :=
  geometricHilbertLinear.mkContinuous 1 (fun f => by
    change ‖geometricHilbertLift f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using geometricHilbertLift_norm_le f)

theorem geometricHilbertContinuous_norm_le_one : ‖geometricHilbertContinuous‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  change ‖geometricHilbertLift f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using geometricHilbertLift_norm_le f

private def geometricCoordinateVector (n : ℕ) : ThresholdHilbert :=
  lp.single 2 n (Real.sqrt (paretoWeight n))

private theorem geometricCoordinateVector_physical (n : ℕ) :
    hilbertGibbsPhysical (geometricCoordinateVector n) =
      fun m => if m = n then 1 else 0 := by
  funext m
  by_cases hm : m = n
  · subst m
    simp [hilbertGibbsPhysical, geometricCoordinateVector,
      ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos n))]
  · simp [hilbertGibbsPhysical, geometricCoordinateVector, hm]

private theorem geometricCoordinateVector_inner (f : ThresholdHilbert) (n : ℕ) :
    inner ℝ f (geometricCoordinateVector n) = paretoWeight n * hilbertGibbsPhysical f n := by
  rw [hilbertGibbs_inner_physical, geometricCoordinateVector_physical]
  simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]

private theorem geometricHilbertContinuous_coordinate_ae (n : ℕ) :
    ∀ᵐ t ∂geometricLatentMeasure,
      geometricHilbertContinuous (geometricCoordinateVector n) t = geometricProbability n t := by
  filter_upwards [geometricHilbertLift_ae (geometricCoordinateVector n)] with t ht
  change geometricHilbertLift (geometricCoordinateVector n) t = _
  rw [ht, geometricCoordinateVector_physical, geometricTransform]
  simp only [ite_mul, one_mul, zero_mul, tsum_ite_eq]

theorem geometricHilbertContinuous_adjoint_formula (g : GeometricLatentL2) (n : ℕ) :
    Integrable (fun t => geometricProbability n t * g t) geometricLatentMeasure ∧
      hilbertGibbsPhysical ((ContinuousLinearMap.adjoint geometricHilbertContinuous) g) n =
        (∫ t, geometricProbability n t * g t ∂geometricLatentMeasure) / paretoWeight n := by
  have hae : (fun t => inner ℝ (g t)
      (geometricHilbertContinuous (geometricCoordinateVector n) t)) =ᵐ[geometricLatentMeasure]
        fun t => geometricProbability n t * g t := by
    filter_upwards [geometricHilbertContinuous_coordinate_ae n] with t ht
    rw [ht, RCLike.inner_apply']
    change g t * geometricProbability n t = geometricProbability n t * g t
    ring
  have hi := (L2.integrable_inner g
    (geometricHilbertContinuous (geometricCoordinateVector n))).congr hae
  refine ⟨hi, ?_⟩
  have hpair := ContinuousLinearMap.adjoint_inner_left geometricHilbertContinuous
    (geometricCoordinateVector n) g
  rw [geometricCoordinateVector_inner, L2.inner_def, integral_congr_ae hae] at hpair
  apply (eq_div_iff (ne_of_gt (paretoWeight_pos n))).mpr
  nlinarith [hpair]

private theorem geometricTransform_row_integral {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) (n : ℕ) :
    (∫ t, geometricProbability n t * geometricTransform f t ∂geometricLatentMeasure) =
      ∑' m, geometricKernel n m * f m := by
  let F : ℕ → ℝ → ℝ := fun m t => f m *
    (geometricProbability n t * geometricProbability m t)
  have hi (m : ℕ) : Integrable (F m) geometricLatentMeasure := by
    rw [latent_eq_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      ((continuous_const.mul ((probability_continuous n).mul
        (probability_continuous m))).intervalIntegrable 0 1)
  have hK (m : ℕ) : (∫ t, geometricProbability n t * geometricProbability m t
      ∂geometricLatentMeasure) = geometricKernel n m := by
    rw [latent_eq_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact geometricProbability_product_integral n m
  have hnorm (m : ℕ) : (∫ t, ‖F m t‖ ∂geometricLatentMeasure) =
      geometricKernel n m * |f m| := by
    calc
      _ = ∫ t, |f m| * (geometricProbability n t * geometricProbability m t)
          ∂geometricLatentMeasure := by
        apply integral_congr_ae
        filter_upwards [latent_ae_mem] with t ht
        dsimp [F]
        rw [abs_mul, abs_of_nonneg
          (mul_nonneg (geometricProbability_nonneg n ⟨ht.1.le,ht.2.le⟩)
            (geometricProbability_nonneg m ⟨ht.1.le,ht.2.le⟩))]
      _ = _ := by rw [integral_const_mul,hK]; ring
  have hs : Summable (fun m => ∫ t, ‖F m t‖ ∂geometricLatentMeasure) := by
    simp only [hnorm]
    exact gibbs_row_summable (f := fun m => |f m|) (by simpa only [abs_abs] using hf) n
  have hswap := integral_tsum_of_summable_integral_norm hi hs
  calc
    _ = ∫ t, ∑' m, F m t ∂geometricLatentMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        change geometricProbability n t * (∑' m, f m * geometricProbability m t) =
          ∑' m, F m t
        rw [← tsum_mul_left]
        apply tsum_congr
        intro m
        dsimp [F]
        ring)
    _ = ∑' m, ∫ t, F m t ∂geometricLatentMeasure := hswap.symm
    _ = _ := by
      apply tsum_congr
      intro m
      dsimp [F]
      rw [integral_const_mul,hK]
      ring

theorem geometricHilbertContinuous_adjoint_comp :
    (ContinuousLinearMap.adjoint geometricHilbertContinuous).comp geometricHilbertContinuous =
      hilbertGibbsContinuous := by
  apply ContinuousLinearMap.ext
  intro f
  apply hilbertSequence_injective
  funext k
  cases k with
  | zero => simp
  | succ n =>
    change hilbertGibbsPhysical ((ContinuousLinearMap.adjoint geometricHilbertContinuous)
      (geometricHilbertContinuous f)) n = hilbertGibbsPhysical (hilbertGibbs f) n
    rw [(geometricHilbertContinuous_adjoint_formula (geometricHilbertContinuous f) n).2,
      hilbertGibbs_physical]
    unfold gibbsAction
    congr 1
    calc
      _ = ∫ t, geometricProbability n t * geometricTransform (hilbertGibbsPhysical f) t
          ∂geometricLatentMeasure := by
        apply integral_congr_ae
        filter_upwards [geometricHilbertLift_ae f] with t ht
        change geometricProbability n t * geometricHilbertLift f t = _
        rw [ht]
      _ = _ := geometricTransform_row_integral (hilbertGibbsPhysical_abs_summable f) n

/-- The original exact target, including the actual series and integral adjoint,
on the entire Hilbert space. -/
theorem geometricHilbertRealizationTarget_proved : GeometricHilbertRealizationTarget := by
  refine ⟨geometricHilbertContinuous, geometricHilbertContinuous_norm_le_one, ?_,
    geometricHilbertContinuous_adjoint_formula, geometricHilbertContinuous_adjoint_comp⟩
  intro f _
  exact geometricHilbertLift_ae f

end
end RiemannResearch.RH.Pareto
