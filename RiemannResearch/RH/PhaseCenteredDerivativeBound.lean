import RiemannResearch.RH.PhaseCenteredOperatorDerivative
import RiemannResearch.RH.PhaseCenteredDerivativeCells
import RiemannResearch.Analysis.LogarithmicMellinBounds

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CompressedMellin

def centeredLogKernel (t x : ℝ) : ℂ :=
  ((Real.log x - Real.log t : ℝ) : ℂ) * (x : ℂ) ^ (-phaseMellinPoint t)
def centeredLogIntegrand (t : ℝ) (f : ThresholdHilbert) (x : ℝ) : ℂ :=
  mellinWeightedStep f x * centeredLogKernel t x

def mellinLogHeadValue (t : ℝ) (N : ℕ) (f : ThresholdHilbert) : ℂ :=
  ∑ n ∈ Finset.range N, (hilbertSequence f (n + 1) : ℂ) * mellinLogCell t n

private theorem centeredLogKernel_norm_sq (t : ℝ) (ht : 0 < t)
    {x : ℝ} (hx : 0 < x) :
    ‖centeredLogKernel t x‖ ^ 2 = Real.log (x / t) ^ 2 / x ^ 2 := by
  rw [centeredLogKernel, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [phaseMellinPoint, Complex.neg_re, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, neg_mul,
    Real.rpow_neg_one]
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ht)]
  ring

private theorem centeredLogKernel_memLp (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    MemLp (centeredLogKernel t) 2 (volume.restrict (Ioi a)) := by
  have hm : Measurable (centeredLogKernel t) := by
    unfold centeredLogKernel
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (RiemannResearch.Analysis.logTail_integrable a t ha ht).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (centeredLogKernel_norm_sq t ht (ha.trans (show a < x from hx))).symm

private theorem centeredLogIntegrand_integrable (t : ℝ) (ht : 0 < t) (f : ThresholdHilbert) :
    IntegrableOn (centeredLogIntegrand t f) (Ioi (1 : ℝ)) :=
  (mellinWeightedStep_memLp f).integrable_mul (centeredLogKernel_memLp 1 t (by norm_num) ht)

private theorem centeredLogIntegrand_physical (t : ℝ) (f : ThresholdHilbert)
    {x : ℝ} (hx : 0 < x) :
    centeredLogIntegrand t f x = (hilbertSequence f ⌊x⌋₊ : ℂ) *
      ((Real.log x - Real.log t : ℝ) : ℂ) * (x : ℂ) ^ (-phaseMellinPoint t - 1) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_sub _ _ hxC, Complex.cpow_one]
  unfold centeredLogIntegrand mellinWeightedStep centeredLogKernel
  ring

/-- The actual derivative is a unit phase times the centered logarithmic pairing. -/
theorem actualDerivative_norm_eq_centeredIntegral (t : ℝ) (f : ThresholdHilbert) :
    ‖actualPhaseCenteredDerivativeOperator t f‖ =
      ‖∫ x in Ioi (1 : ℝ), centeredLogIntegrand t f x‖ := by
  have he : actualPhaseCenteredDerivativeOperator t f =
      (-Complex.I * phaseMellinForward t) *
        ∫ x in Ioi (1 : ℝ), centeredLogIntegrand t f x := by
    rw [actualPhaseCenteredDerivativeOperator_apply, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [centeredLogIntegrand_physical t f (zero_lt_one.trans (show 1 < x from hx))]
    push_cast
    ring
  rw [he, norm_mul, norm_mul, norm_neg, Complex.norm_I, phaseMellinForward_norm]
  ring

/-- Cauchy--Schwarz for the full actual derivative tail, in the original physical norm. -/
theorem centeredLogIntegral_tail_bound (a t : ℝ) (ha : 1 ≤ a) (ht : 0 < t)
    (f : ThresholdHilbert) :
    ‖∫ x in Ioi a, centeredLogIntegrand t f x‖ ^ 2 ≤
      ‖f‖ ^ 2 * ∫ x in Ioi a, Real.log (x / t) ^ 2 / x ^ 2 := by
  have ha0 := zero_lt_one.trans_le ha
  have hs : Ioi a ⊆ Ioi (1 : ℝ) := fun x hx => ha.trans_lt hx
  have hF : MemLp (mellinWeightedStep f) 2 (volume.restrict (Ioi a)) :=
    (mellinWeightedStep_memLp f).mono_measure (Measure.restrict_mono hs le_rfl)
  have hK := centeredLogKernel_memLp a t ha0 ht
  have h := RemoteLaplaceTail.norm_integral_mul_sq_le hF hK
  have hE : (∫ x in Ioi a, ‖mellinWeightedStep f x‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    rw [← mellinWeightedStep_energy]
    apply setIntegral_mono_set
      ((memLp_two_iff_integrable_sq_norm
        (mellinWeightedStep_memLp f).aestronglyMeasurable).mp (mellinWeightedStep_memLp f))
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    exact Filter.Eventually.of_forall hs
  have hKE : (∫ x in Ioi a, ‖centeredLogKernel t x‖ ^ 2) =
      ∫ x in Ioi a, Real.log (x / t) ^ 2 / x ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact centeredLogKernel_norm_sq t ht (ha0.trans (show a < x from hx))
  change ‖∫ x in Ioi a, centeredLogIntegrand t f x‖ ^ 2 ≤ _ at h
  rw [hKE] at h
  exact h.trans (mul_le_mul_of_nonneg_right hE (integral_nonneg (fun x =>
    div_nonneg (sq_nonneg _) (sq_nonneg _))))

/-- Finite weighted Cauchy--Schwarz with exact coefficient energy. -/
theorem mellinLogHeadValue_bound (t : ℝ) (ht : 1 ≤ t) (N : ℕ)
    (hN : (N : ℝ) + 1 ≤ t) (f : ThresholdHilbert) :
    ‖mellinLogHeadValue t N f‖ ^ 2 ≤ (28 / t) * ‖f‖ ^ 2 := by
  let r := fun n => |hilbertSequence f (n + 1)| * ‖mellinLogCell t n‖
  let u := fun n => paretoWeight n * hilbertSequence f (n + 1) ^ 2
  let v := fun n => ‖mellinLogCell t n‖ ^ 2 / paretoWeight n
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.range N)
    (r := r) (f := u) (g := v)
    (fun n _ => mul_nonneg (paretoWeight_pos n).le (sq_nonneg _))
    (fun n _ => div_nonneg (sq_nonneg _) (paretoWeight_pos n).le)
    (by
      intro n hn
      dsimp [r, u, v]
      rw [mul_pow, sq_abs]
      field_simp [(paretoWeight_pos n).ne'])
  have hu : (∑ n ∈ Finset.range N, u n) ≤ ‖f‖ ^ 2 := by
    have hseq : ∀ n, u n = (f n) ^ 2 := by
      intro n
      change paretoWeight n * hilbertSequence f (n + 1) ^ 2 = _
      rw [← positiveWeight_succ]
      exact hilbertSequence_weighted_square f n
    simp_rw [hseq]
    rw [hilbert_norm_sq]
    exact Summable.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _)
      (hilbert_coordinate_square_summable f)
  have hv : (∑ n ∈ Finset.range N, v n) ≤ 28 / t :=
    mellinLogCell_head_energy t ht N hN
  have hn : ‖mellinLogHeadValue t N f‖ ≤ ∑ n ∈ Finset.range N, r n := by
    simpa only [mellinLogHeadValue, r, norm_mul, Complex.norm_real, Real.norm_eq_abs] using!
      norm_sum_le (Finset.range N) (fun n => (hilbertSequence f (n + 1) : ℂ) * mellinLogCell t n)
  have hr : 0 ≤ ∑ n ∈ Finset.range N, r n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hsq : ‖mellinLogHeadValue t N f‖ ^ 2 ≤ (∑ n ∈ Finset.range N, r n) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hr).mpr hn
  calc
    _ ≤ (∑ n ∈ Finset.range N, u n) * ∑ n ∈ Finset.range N, v n := hsq.trans hCS
    _ ≤ ‖f‖ ^ 2 * (28 / t) :=
      mul_le_mul hu hv
        (Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (paretoWeight_pos n).le))
        (sq_nonneg _)
    _ = _ := by ring

private theorem centeredLog_cell_integral (t : ℝ) (f : ThresholdHilbert) (n : ℕ) :
    (∫ x in derivativeUnitCell n, centeredLogIntegrand t f x) =
      (hilbertSequence f (n + 1) : ℂ) * mellinLogCell t n := by
  unfold mellinLogCell
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ico
  intro x hx
  dsimp only
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1) hx.1
  rw [centeredLogIntegrand_physical t f hx0]
  have hfloor : ⌊x⌋₊ = n + 1 := by
    apply Nat.floor_eq_on_Ico
    simpa only [derivativeUnitCell, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hx
  rw [hfloor]
  ring

/-- The full derivative pairing splits exactly at an integer physical boundary. -/
theorem centeredLogIntegral_split (t : ℝ) (ht : 0 < t) (N : ℕ) (f : ThresholdHilbert) :
    (∫ x in Ioi (1 : ℝ), centeredLogIntegrand t f x) =
      mellinLogHeadValue t N f +
        ∫ x in Ioi ((N : ℝ) + 1), centeredLogIntegrand t f x := by
  have hi := centeredLogIntegrand_integrable t ht f
  have hinterval (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (centeredLogIntegrand t f) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hi.mono_set (fun x hx => ha.trans_lt hx.1)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) + 1) (n := N)
    (f := centeredLogIntegrand t f)
    (fun k hk => hinterval _ _
      (by have h := Nat.cast_nonneg (α := ℝ) k; linarith) (by push_cast; linarith))
  simp only [Nat.cast_zero, zero_add] at hsum
  have he : (∫ x in (1 : ℝ)..((N : ℝ) + 1), centeredLogIntegrand t f x) =
      mellinLogHeadValue t N f := by
    rw [← hsum]
    unfold mellinLogHeadValue
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_of_le (by push_cast; linarith),
      ← integral_Ico_eq_integral_Ioc]
    convert! centeredLog_cell_integral t f n using 1 <;>
      simp only [derivativeUnitCell, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (hinterval 1 ((N : ℝ) + 1) le_rfl
      (by have h := Nat.cast_nonneg (α := ℝ) N; linarith))
    (hi.mono_set (fun x hx => (show (1 : ℝ) ≤ (N : ℝ) + 1 by
      have h := Nat.cast_nonneg (α := ℝ) N; linarith).trans_lt hx))
  rw [he] at hsplit
  exact hsplit.symm

/-- Concrete complete operator derivative estimate, with the original provider constant. -/
theorem actualPhaseCenteredDerivativeOperator_apply_bound (t : ℝ) (ht : 1 ≤ t)
    (f : ThresholdHilbert) :
    ‖actualPhaseCenteredDerivativeOperator t f‖ ^ 2 ≤ (82 / t) * ‖f‖ ^ 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [actualDerivative_norm_eq_centeredIntegral]
  by_cases ht2 : t ≤ 2
  · have h := centeredLogIntegral_tail_bound 1 t le_rfl ht0 f
    have htail := RiemannResearch.Analysis.logTail_one_le_two t ht ht2
    have hc : (2 : ℝ) ≤ 82 / t := by rw [le_div_iff₀ ht0]; linarith
    exact h.trans ((mul_le_mul_of_nonneg_left htail (sq_nonneg _)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖f‖)]))
  · let M : ℕ := ⌊t⌋₊
    have hM0 : 1 ≤ M := (Nat.le_floor_iff ht0.le).mpr (by simpa using ht)
    have hM : (M : ℝ) ≤ t := Nat.floor_le ht0.le
    have hMt : t < (M : ℝ) + 1 := Nat.lt_floor_add_one t
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
    have hhalf : t / 2 ≤ (M : ℝ) := by linarith
    have hcount : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hM0)
    have hhead := mellinLogHeadValue_bound t ht (M - 1) (by rw [hcount]; exact hM) f
    have htail := centeredLogIntegral_tail_bound (M : ℝ) t hM1 ht0 f
    have htail' := RiemannResearch.Analysis.logTail_le_four_div (M : ℝ) t ht0 hhalf hM
    have htailB : ‖∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x‖ ^ 2 ≤
        (4 / t) * ‖f‖ ^ 2 := by
      exact htail.trans (by nlinarith [mul_le_mul_of_nonneg_left htail' (sq_nonneg ‖f‖)])
    rw [centeredLogIntegral_split t ht0 (M - 1) f, hcount]
    have hnorm := norm_add_le (mellinLogHeadValue t (M - 1) f)
      (∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x)
    have hsquared :
        ‖mellinLogHeadValue t (M - 1) f +
          ∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x‖ ^ 2 ≤
        (‖mellinLogHeadValue t (M - 1) f‖ +
          ‖∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
    have hp := sq_nonneg (‖mellinLogHeadValue t (M - 1) f‖ -
      ‖∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x‖)
    have hc : (64 : ℝ) / t ≤ 82 / t := div_le_div_of_nonneg_right (by norm_num) ht0.le
    have hscale := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖f‖)
    calc
      _ ≤ (‖mellinLogHeadValue t (M - 1) f‖ +
          ‖∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x‖) ^ 2 := hsquared
      _ ≤ 2 * (‖mellinLogHeadValue t (M - 1) f‖ ^ 2 +
          ‖∫ x in Ioi (M : ℝ), centeredLogIntegrand t f x‖ ^ 2) := by
        nlinarith only [hp]
      _ ≤ 2 * ((28 / t) * ‖f‖ ^ 2 + (4 / t) * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hhead htailB) (by norm_num)
      _ = (64 / t) * ‖f‖ ^ 2 := by ring
      _ ≤ (82 / t) * ‖f‖ ^ 2 := hscale

/-- The quantitative operator-norm estimate required by the named provider. -/
theorem actualPhaseCenteredDerivativeOperator_norm_bound (t : ℝ) (ht : 1 ≤ t) :
    ‖actualPhaseCenteredDerivativeOperator t‖ ^ 2 ≤ 82 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hR : 0 ≤ 82 / t := by positivity
  have hbound : ‖actualPhaseCenteredDerivativeOperator t‖ ≤ Real.sqrt (82 / t) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    have h := actualPhaseCenteredDerivativeOperator_apply_bound t ht f
    have he : (Real.sqrt (82 / t) * ‖f‖) ^ 2 = (82 / t) * ‖f‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR]
    have hp : 0 ≤ Real.sqrt (82 / t) * ‖f‖ := by positivity
    nlinarith [norm_nonneg (actualPhaseCenteredDerivativeOperator t f)]
  have hs := Real.sq_sqrt hR
  nlinarith [norm_nonneg (actualPhaseCenteredDerivativeOperator t),
    Real.sqrt_nonneg (82 / t)]

end RiemannResearch.RH.Pareto.CompressedMellin
