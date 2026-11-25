import RiemannResearch.Analysis.MontgomeryPrimeProbeMixedKernel
import RiemannResearch.Analysis.MontgomeryMovingPrimeProbeTrace

/-! # Sharp moving widths for the arithmetic prime probe -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set MontgomeryPositiveGap ZeroOrdinate
open RiemannResearch.RH.Pareto.SpectralObstruction
open scoped Topology BigOperators

/-- The square error between the two Fourier amplitudes. -/
def primeProbeFourierErrorEnergy (T q : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..q, ‖primeFourierProbe T u-primeContinuumProbe u‖^2

/-- The signed difference between the two energies. -/
def primeProbeEnergyExcess (T q : ℝ) : ℝ := primeProbeEnergy T q - (q-sineGapMass q)

private theorem angular_square {L : ℝ} (hL : 0 < L) (q : ℝ) (f F : ℝ → ℂ)
    (h : ∀ t, F t = (L : ℂ)*f (L*t/(2*Real.pi))) :
    (∫ u in (0:ℝ)..q, ‖f u‖^2) =
      1/(2*Real.pi*L) * ∫ t in (0:ℝ)..(2*Real.pi*q/L), ‖F t‖^2 := by
  let k := L/(2*Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  have he (t : ℝ) : ‖F t‖^2 = L^2*‖f (k*t)‖^2 := by
    rw [h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL,mul_pow]
    dsimp [k]
    ring_nf
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left
    (fun u => ‖f u‖^2) hk.ne',mul_zero,smul_eq_mul,
    show k*(2*Real.pi*q/L)=q by dsimp [k]; field_simp]
  dsimp [k]
  field_simp
  <;> ring

theorem primeProbeFourierErrorEnergy_eq_band {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    primeProbeFourierErrorEnergy T q = (q/(Real.log T)^2) *
      probeBandSquare (2*Real.pi*q/Real.log T) (primeLogDiscrepancy (Real.log T)) := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [primeProbeFourierErrorEnergy]
  let L := Real.log T
  have hL : 0 < L := Real.log_pos hT
  have h := angular_square hL q (fun u => primeFourierProbe T u-primeContinuumProbe u)
    (primeLogDiscrepancy L) (fun t => by
      simpa [L,Real.exp_log (zero_lt_one.trans hT)] using primeLogDiscrepancy_eq_scaled hL t)
  rw [primeProbeFourierErrorEnergy, h, probeBandSquare, probeBandMean]
  change _ = q/L^2*((∫ t in (0:ℝ)..(2*Real.pi*q/L), ‖primeLogDiscrepancy L t‖^2)/(2*Real.pi*q/L))
  field_simp [hL.ne',hq.ne',Real.pi_ne_zero]
  <;> ring

/-- Exact physical-space representation of the signed mixed term, including zero width. -/
theorem primeProbeEnergyExcess_sub_fourier_eq {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    let L := Real.log T
    primeProbeEnergyExcess T q - primeProbeFourierErrorEnergy T q =
      primeLogTest L (probeMixedKernel (2*Real.pi*q/L) L)/(Real.pi*L) := by
  let L := Real.log T
  let B := 2*Real.pi*q/L
  have hL : 0 < L := Real.log_pos hT
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h1 := angular_square hL q (primeFourierProbe T) (primeLogPolynomial L) (fun t => by
    simpa [L,Real.exp_log (zero_lt_one.trans hT)] using logPolynomial_eq_scaled_probe hL t)
  have h2 := angular_square hL q primeContinuumProbe (logBoxProbe L)
    (logBoxProbe_eq_scaled_continuum hL)
  have h3 := angular_square hL q (fun u => primeFourierProbe T u-primeContinuumProbe u)
    (primeLogDiscrepancy L) (fun t => by
      simpa [L,Real.exp_log (zero_lt_one.trans hT)] using primeLogDiscrepancy_eq_scaled hL t)
  have hc (u : ℝ) : Real.sinc (Real.pi*u)^2 = ‖primeContinuumProbe u‖^2 := by
    rw [norm_primeContinuumProbe_eq,sq_abs]
  have hp (t : ℝ) : ‖primeLogPolynomial L t‖^2-‖logBoxProbe L t‖^2-‖primeLogDiscrepancy L t‖^2 =
      2*probePair (logBoxProbe L t) (primeLogDiscrepancy L t) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,primeLogDiscrepancy,Complex.sub_re,
      Complex.sub_im,probePair]
    ring
  have hu := ((continuous_primeLogPolynomial L).norm.pow 2).intervalIntegrable (μ := volume) 0 B
  have hb := ((continuous_logBoxProbe hL).norm.pow 2).intervalIntegrable (μ := volume) 0 B
  have hd := ((continuous_primeLogDiscrepancy hL).norm.pow 2).intervalIntegrable (μ := volume) 0 B
  have he := intervalIntegral.integral_congr (a := (0:ℝ)) (b := B) (μ := volume) (fun t _ => hp t)
  rw [intervalIntegral.integral_sub
      (f := fun t => ‖primeLogPolynomial L t‖^2-‖logBoxProbe L t‖^2)
      (g := fun t => ‖primeLogDiscrepancy L t‖^2) (hu.sub hb) hd,
    intervalIntegral.integral_sub (f := fun t => ‖primeLogPolynomial L t‖^2)
      (g := fun t => ‖logBoxProbe L t‖^2) hu hb,
    intervalIntegral.integral_const_mul, primeLogDiscrepancy_mixed_eq hL hB] at he
  dsimp only
  rw [primeProbeEnergyExcess,primeProbeEnergy,← primeSineHoleMass_eq,primeProbeFourierErrorEnergy]
  simp_rw [hc]
  rw [h1,h2,h3]
  change 1/(2*Real.pi*L)*_ - 1/(2*Real.pi*L)*_ - 1/(2*Real.pi*L)*_ =
    primeLogTest L (probeMixedKernel B L)/(Real.pi*L)
  rw [← mul_sub,← mul_sub,he]
  ring

/-- Uniform `O(1/log T)` mixed term, with no upper bound on width. -/
theorem primeProbe_mixed_error_uniform :
    ∃ K > (0 : ℝ), ∀ {T q : ℝ}, 1 < T → 2 ≤ Real.log T → 0 ≤ q →
      |primeProbeEnergyExcess T q-primeProbeFourierErrorEnergy T q| ≤ K/Real.log T := by
  obtain ⟨C,hC,h⟩ := probeMixedKernel_test_uniform
  refine ⟨C/Real.pi,by positivity,fun {T q} hT' hT hq => ?_⟩
  have hL := Real.log_pos hT'
  rw [primeProbeEnergyExcess_sub_fourier_eq hT' hq,abs_div,abs_of_pos (mul_pos Real.pi_pos hL)]
  calc
    _ ≤ C/(Real.pi*Real.log T) := div_le_div_of_nonneg_right
      (h (by positivity) hT) (by positivity)
    _ = _ := by ring

private theorem bandSquare_uniform :
    ∃ C > (0:ℝ), ∀ {B L : ℝ}, 0 < B → 1 ≤ L → probeBandSquare B (primeLogDiscrepancy L) ≤ C := by
  obtain ⟨A,hA,hh⟩ := primeLogDiscrepancy_band_diagonal
  obtain ⟨D,hD,hr⟩ := logMertensRemainder_inverse_square
  let J := ∫ y in Ioi (0:ℝ), |logMertensRemainder y|
  have hJ : 0 ≤ J := integral_nonneg fun _ => abs_nonneg _
  let W := |mertensCenter|+D+J
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨primeProbeDiagonal+A+W^2,by have := primeProbeDiagonal_pos; positivity,
    fun {B L} hB hL => ?_⟩
  have hL0 : 0 < L := by linarith
  by_cases hbig : 1 ≤ B
  · let z := Real.sqrt (Real.sqrt B)
    have hz : 1 ≤ z := by dsimp [z]; exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hbig)
    have he : z^4 = B := by
      dsimp [z]
      rw [show (4:ℕ) = 2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt hB.le]
    have h := (abs_le.mp (hh hz hL)).2
    rw [he] at h
    linarith only [h,primeProbePartialDiagonal_le (min z L),div_le_self hA.le hz,sq_nonneg W]
  · have hpoint (t : ℝ) (ht : t ∈ Icc 0 B) : ‖primeLogDiscrepancy L t‖ ≤ W := by
      have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
      rw [primeLogDiscrepancy_abel hL0]
      have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun y =>
        (logMertensRemainder y:ℂ)*phase y t) hL0.le
      simp only [norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs] at hnorm
      have hi : IntegrableOn (fun y => |logMertensRemainder y|) (Ioi 0) :=
        integrableOn_logMertensRemainder.abs
      have hJ' : (∫ y in (0:ℝ)..L, |logMertensRemainder y|) ≤ J := by
        rw [intervalIntegral.integral_of_le hL0.le]
        exact setIntegral_mono_set hi (Eventually.of_forall fun _ => abs_nonneg _)
          (Eventually.of_forall fun _ hy => hy.1)
      have hR : |logMertensRemainder L| ≤ D := (hr L hL0.le).trans
        (div_le_self hD.le (by nlinarith [sq_nonneg L]))
      apply (norm_sub_le _ _).trans
      apply (add_le_add (norm_add_le _ _) le_rfl).trans
      simp only [norm_mul,phase_norm,mul_one,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs]
      have hm := mul_le_mul ht' (hnorm.trans hJ') (norm_nonneg _) zero_le_one
      dsimp [W]
      linarith
    have ht := probeBandMean_mono hB.le ((continuous_primeLogDiscrepancy hL0).norm.pow 2)
      (g := fun _ => W^2) continuous_const
      (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hpoint t ht) 2)
    rw [probeBandMean_const hB.ne'] at ht
    change probeBandSquare B (primeLogDiscrepancy L) ≤ W^2 at ht
    linarith only [ht,primeProbeDiagonal_pos,hA]

private theorem primeProbeFourierErrorEnergy_large :
    ∃ K > (0:ℝ), ∀ {T q : ℝ}, 1 < T → 1 ≤ Real.log T → 0 ≤ q →
      primeProbeFourierErrorEnergy T q ≤ K*(q/(Real.log T)^2) := by
  obtain ⟨C,hC,h⟩ := bandSquare_uniform
  refine ⟨C,hC,fun {T q} hT hL hq => ?_⟩
  rcases hq.eq_or_lt with rfl | hq
  · simp [primeProbeFourierErrorEnergy]
  rw [primeProbeFourierErrorEnergy_eq_band hT hq.le,mul_comm C]
  exact mul_le_mul_of_nonneg_left (h (by have := Real.log_pos hT; positivity) hL) (by positivity)

/-- The integrated Fourier error is bounded by a constant times `q / log(T)^2` at every
positive log height and every nonnegative width. -/
theorem primeProbeFourierErrorEnergy_uniform :
    ∃ K > (0:ℝ), ∀ {T q : ℝ}, 1 < T → 0 ≤ q →
      primeProbeFourierErrorEnergy T q ≤ K*(q/(Real.log T)^2) := by
  obtain ⟨C,hC,h⟩ := primeProbeFourierErrorEnergy_large
  let D := 2+(Real.log 4+4)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨max C (D^2),lt_of_lt_of_le hC (le_max_left _ _),fun {T q} hT hq => ?_⟩
  have hL := Real.log_pos hT
  by_cases hlarge : 1 ≤ Real.log T
  · exact (h hT hlarge hq).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hc : Continuous primeContinuumProbe := by
    rw [funext primeContinuumProbe_eq]
    exact continuous_logPhaseKernel.comp (by fun_prop)
  have hp : Continuous (primeFourierProbe T) := by unfold primeFourierProbe; fun_prop
  have hpoint (u : ℝ) : ‖primeFourierProbe T u-primeContinuumProbe u‖ ≤ D/Real.log T := by
    have hb := norm_primeFourierProbe_le hT u
    have hs : ‖primeContinuumProbe u‖ ≤ 1 := by
      rw [norm_primeContinuumProbe_eq]
      exact Real.abs_sinc_le_one _
    apply (norm_sub_le _ _).trans ((add_le_add hb hs).trans ?_)
    dsimp [D]
    field_simp [hL.ne']
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hq
    (f := fun u => ‖primeFourierProbe T u-primeContinuumProbe u‖^2)
    (g := fun _ => (D/Real.log T)^2)
    (((hp.sub hc).norm.pow 2).intervalIntegrable 0 q) intervalIntegrable_const
    (fun u _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint u) 2)
  rw [intervalIntegral.integral_const,smul_eq_mul,sub_zero] at hi
  calc
    _ ≤ q*(D/Real.log T)^2 := hi
    _ = D^2*(q/(Real.log T)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private theorem fourier_nonneg {T q : ℝ} (hq : 0 ≤ q) : 0 ≤ primeProbeFourierErrorEnergy T q :=
  intervalIntegral.integral_nonneg hq (fun _ _ => sq_nonneg _)

/-- A finite-height signed estimate uniform over all nonnegative widths. -/
theorem primeProbeEnergyExcess_uniform :
    ∃ K > (0:ℝ), ∀ {T q : ℝ}, 1 < T → 2 ≤ Real.log T → 0 ≤ q →
      |primeProbeEnergyExcess T q| ≤ K*(1/Real.log T + q/(Real.log T)^2) := by
  obtain ⟨A,hA,ha⟩ := primeProbe_mixed_error_uniform
  obtain ⟨C,hC,hc⟩ := primeProbeFourierErrorEnergy_uniform
  refine ⟨A+C,by positivity,fun {T q} hT hL hq => ?_⟩
  have h1 := ha hT hL hq
  have h2 := hc hT hq
  have h3 := abs_add_le (primeProbeEnergyExcess T q-primeProbeFourierErrorEnergy T q)
    (primeProbeFourierErrorEnergy T q)
  rw [sub_add_cancel,abs_of_nonneg (fourier_nonneg hq)] at h3
  calc
    _ ≤ A/Real.log T + C*(q/(Real.log T)^2) := h3.trans (add_le_add h1 h2)
    _ ≤ _ := by
      have hL' := Real.log_pos hT
      rw [show A/Real.log T = A*(1/Real.log T) by ring,add_mul,mul_add,mul_add]
      linarith only [mul_nonneg hC.le (one_div_pos.mpr hL').le,
        mul_nonneg hA.le (div_nonneg hq (sq_nonneg (Real.log T)))]

private theorem mixed_tendsto {q : ℝ → ℝ} (hq : ∀ᶠ T in atTop, 0 ≤ q T) :
    Tendsto (fun T : ℝ => primeProbeEnergyExcess T (q T)-primeProbeFourierErrorEnergy T (q T))
      atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := primeProbe_mixed_error_uniform
  apply squeeze_zero_norm' _ (Real.tendsto_log_atTop.const_div_atTop C)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2,eventually_gt_atTop (1:ℝ),hq]
    with T hL hT hqT
  exact h hT hL hqT

theorem primeProbeFourierErrorEnergy_superlog (q : ℝ → ℝ)
    (h : Tendsto (fun T : ℝ => q T/Real.log T) atTop atTop) :
    Tendsto (fun T : ℝ => primeProbeFourierErrorEnergy T (q T)/(q T/(Real.log T)^2))
      atTop (𝓝 primeProbeDiagonal) := by
  have hB : Tendsto (fun T : ℝ => 2*Real.pi*q T/Real.log T) atTop atTop := by
    simpa only [mul_div_assoc] using h.const_mul_atTop (show 0 < 2*Real.pi by positivity)
  apply (primeLogDiscrepancy_cesaro Real.tendsto_log_atTop hB).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),h.eventually_gt_atTop 0] with T hT hq
  have hL := Real.log_pos hT
  have hqT := (div_pos_iff_of_pos_right hL).1 hq
  rw [primeProbeFourierErrorEnergy_eq_band hT hqT.le]
  field_simp

/-- Exact signed superlogarithmic profile, even when the excess itself goes to zero. -/
theorem primeProbeEnergyExcess_superlog (q : ℝ → ℝ)
    (h : Tendsto (fun T : ℝ => q T/Real.log T) atTop atTop) :
    Tendsto (fun T : ℝ => primeProbeEnergyExcess T (q T)/(q T/(Real.log T)^2))
      atTop (𝓝 primeProbeDiagonal) := by
  obtain ⟨C,_,hc⟩ := primeProbe_mixed_error_uniform
  have hm : Tendsto (fun T : ℝ =>
      (primeProbeEnergyExcess T (q T)-primeProbeFourierErrorEnergy T (q T))/(q T/(Real.log T)^2))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (h.const_div_atTop C)
    filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 2,
      h.eventually_gt_atTop 0] with T hT hL hq
    have hL' := Real.log_pos hT
    have hqT := (div_pos_iff_of_pos_right hL').1 hq
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < q T/(Real.log T)^2)]
    calc
      _ ≤ (C/Real.log T)/(q T/(Real.log T)^2) :=
        div_le_div_of_nonneg_right (hc hT hL hqT.le) (by positivity)
      _ = _ := by field_simp
  have hp := hm.add (primeProbeFourierErrorEnergy_superlog q h)
  simpa only [zero_add,sub_div,sub_add_cancel] using hp

/-- The critical boundary coefficient at any positive finite multiple of log squared. -/
theorem primeProbeEnergyExcess_critical {q : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun T : ℝ => q T/(Real.log T)^2) atTop (𝓝 α)) :
    Tendsto (fun T : ℝ => primeProbeEnergyExcess T (q T)) atTop (𝓝 (α*primeProbeDiagonal)) := by
  have hsuper : Tendsto (fun T : ℝ => q T/Real.log T) atTop atTop := by
    apply (h.pos_mul_atTop hα Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    field_simp [(Real.log_pos hT).ne']
  apply (h.mul (primeProbeEnergyExcess_superlog q hsuper)).congr'
  filter_upwards [h.eventually (lt_mem_nhds hα)] with T hq
  let r := q T/(Real.log T)^2
  have hr : r ≠ 0 := hq.ne'
  change r*(primeProbeEnergyExcess T (q T)/r) = _
  field_simp [hr]

theorem primeProbeEnergy_moving_sublog_sq {q : ℝ → ℝ} (hq : ∀ᶠ T in atTop, 0 ≤ q T)
    (hs : Tendsto (fun T : ℝ => q T/(Real.log T)^2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => primeProbeEnergyExcess T (q T)) atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := primeProbeFourierErrorEnergy_uniform
  have hi : Tendsto (fun T : ℝ => primeProbeFourierErrorEnergy T (q T)) atTop (𝓝 0) := by
    apply squeeze_zero' (hq.mono fun T ht => fourier_nonneg ht) _ (by simpa using hs.const_mul C)
    filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,hq]
      with T hT hL ht
    exact h hT ht
  simpa only [zero_add,sub_add_cancel] using (mixed_tendsto hq).add hi

/-- The arithmetic energy converges to the sine-model energy exactly below the quadratic scale. -/
theorem primeProbeEnergyExcess_tendsto_zero_iff {q : ℝ → ℝ} (hq : ∀ᶠ T in atTop, 0 ≤ q T) :
    Tendsto (fun T : ℝ => primeProbeEnergyExcess T (q T)) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => q T/(Real.log T)^2) atTop (𝓝 0) := by
  refine ⟨fun he => ?_,primeProbeEnergy_moving_sublog_sq hq⟩
  have hi : Tendsto (fun T : ℝ => primeProbeFourierErrorEnergy T (q T)) atTop (𝓝 0) := by
    simpa only [sub_sub_cancel,sub_zero] using he.sub (mixed_tendsto hq)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hq] with T hT
    exact ha.trans_le (div_nonneg hT (sq_nonneg _))
  · intro a ha
    let w := fun T : ℝ => a*(Real.log T)^2
    have hw (T : ℝ) : 0 ≤ w T := mul_nonneg ha.le (sq_nonneg _)
    have hwlim : Tendsto (fun T : ℝ => w T/(Real.log T)^2) atTop (𝓝 a) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
      dsimp [w]
      field_simp [(Real.log_pos hT).ne']
    have hW := (primeProbeEnergyExcess_critical ha hwlim).sub
      (mixed_tendsto (Eventually.of_forall hw))
    simp only [sub_sub_cancel,sub_zero] at hW
    have haD := mul_pos ha primeProbeDiagonal_pos
    filter_upwards [hi.eventually (gt_mem_nhds (half_pos haD)),
      hW.eventually (lt_mem_nhds (half_lt_self haD)),eventually_gt_atTop (1:ℝ)] with T hlt1 hlt2 hT
    have hlt := hlt1.trans hlt2
    apply (div_lt_iff₀ (sq_pos_of_pos (Real.log_pos hT))).2
    by_contra! hge
    have hp : Continuous (primeFourierProbe T) := by unfold primeFourierProbe; fun_prop
    have hc : Continuous primeContinuumProbe := by
      rw [funext primeContinuumProbe_eq]
      exact continuous_logPhaseKernel.comp (by fun_prop)
    have hmono : primeProbeFourierErrorEnergy T (w T) ≤ primeProbeFourierErrorEnergy T (q T) := by
      exact intervalIntegral.integral_mono_interval le_rfl (hw T) hge
        (Eventually.of_forall fun _ => sq_nonneg _)
        (((hp.sub hc).norm.pow 2).intervalIntegrable 0 (q T))
    exact (not_le_of_gt hlt) hmono

theorem movingPrimeProbeTrace_sublog_sq_iff {q : ℝ → ℝ} (hq : ∀ᶠ T in atTop, 0 ≤ q T)
    (h : Tendsto (fun T : ℝ => q T/(Real.log T)^2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + primeProbeEnergy T (q T)) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + (q T-sineGapMass (q T)))
        atTop (𝓝 0) :=
  movingPrimeProbeTrace_iff_sineHole (primeProbeEnergy_moving_sublog_sq hq h)

theorem movingPrimeProbeTrace_critical_iff {q : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun T : ℝ => q T/(Real.log T)^2) atTop (𝓝 α)) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + primeProbeEnergy T (q T)) atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T))
        atTop (𝓝 (-(1/2+α*primeProbeDiagonal))) := by
  have hq : Tendsto q atTop atTop := by
    have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by decide)
    apply (h.pos_mul_atTop hα (hpow.comp Real.tendsto_log_atTop)).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (Real.log_pos hT).ne')
  exact movingPrimeProbeTrace_iff_sampled_limit_of_energyDefect hq
    (primeProbeEnergyExcess_critical hα h)

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeFourierErrorEnergy_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeFourierErrorEnergy_uniform

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbe_mixed_error_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbe_mixed_error_uniform

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergyExcess_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergyExcess_uniform

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeFourierErrorEnergy_superlog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeFourierErrorEnergy_superlog

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergyExcess_superlog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergyExcess_superlog

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergyExcess_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergyExcess_critical

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergyExcess_tendsto_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergyExcess_tendsto_zero_iff

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.movingPrimeProbeTrace_critical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms movingPrimeProbeTrace_critical_iff

end RiemannResearch.Analysis.MontgomeryPrimeTrace
