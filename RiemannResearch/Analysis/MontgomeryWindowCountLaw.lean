import RiemannResearch.Analysis.MicroscopicCountTail
import RiemannResearch.Analysis.MontgomeryMicroscopicCovariance

/-! # From the limiting distribution of a zero count to Dyson pair correlation

A bounded fourth moment supplies uniform integrability of the square. Hence
weak convergence of the translated counts at positive rational widths, to
laws with the sine-process second moments, implies strict positive-gap PCC
and density one of simple critical-line zeros. Weak convergence of the
actual counts to these laws is an analytic hypothesis. See Arias de Reyna
and Rodgers, arXiv:2311.13441, for the full point-process equivalences.
-/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroWindowVariance ActualZeroCollisionCertificate
open MicroscopicCountTail OrdinateWindowVariance

/-- Bounded continuous tests for the translated count distribution. Subtracting
the value at zero permits integration over the line, since the count vanishes
outside the sampling interval. Its uniform probability measure has mass one. -/
def WindowCountWeakLimit (q : ℝ) (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ f : ℝ → ℝ, Continuous f → f 0 = 0 →
    (∃ B : ℝ, ∀ x : ℝ, |f x| ≤ B) →
    Tendsto (fun T => (∫ t : ℝ, f (actualWindowCount T
      (q / (Real.log T / (2*Real.pi))) t)) / T) atTop (𝓝 (∫ x, f x ∂ν))

private theorem cap_second_error {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X : α → ℝ} (hm : Measurable X) (h₂ : Integrable (fun t => X t ^ 2) μ)
    (h₄ : Integrable (fun t => X t ^ 4) μ) {M : ℝ} (hM : 0 < M) :
    (∫ t, min (X t ^ 2) M ∂μ) ≤ ∫ t, X t ^ 2 ∂μ ∧
    (∫ t, X t ^ 2 ∂μ) ≤ (∫ t, min (X t ^ 2) M ∂μ) + (∫ t, X t ^ 4 ∂μ)/M := by
  have hcap : Integrable (fun t => min (X t ^ 2) M) μ := by
    apply h₂.mono' (((hm.pow_const 2).min measurable_const).aestronglyMeasurable)
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) hM.le)]
    exact min_le_left _ _
  refine ⟨integral_mono hcap h₂ (fun t => min_le_left _ _),?_⟩
  rw [← integral_div, ← integral_add hcap (h₄.div_const M)]
  apply integral_mono h₂ (hcap.add (h₄.div_const M))
  intro t
  change X t^2 ≤ min (X t^2) M + X t^4/M
  by_cases ht : X t ^ 2 ≤ M
  · rw [min_eq_left ht]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hM.le)
  · rw [min_eq_right (le_of_not_ge ht)]
    have hsq : X t ^ 2 ≤ X t ^ 4 / M := by
      apply (le_div_iff₀ hM).mpr
      calc
        _ ≤ (X t ^ 2)*(X t ^ 2) := mul_le_mul_of_nonneg_left (le_of_not_ge ht) (sq_nonneg _)
        _ = _ := by ring
    linarith

private theorem model_capped_square_limit (ν : Measure ℝ)
    (h₂ : Integrable (fun x : ℝ => x^2) ν) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, min (x^2) ((n:ℝ)+1) ∂ν) atTop
      (𝓝 (∫ x : ℝ, x^2 ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x^2)
  · intro n
    exact (show Continuous (fun x : ℝ => min (x^2) ((n:ℝ)+1)) by fun_prop).aestronglyMeasurable
  · exact h₂
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (le_min (sq_nonneg _) (by positivity))]
    exact min_le_left _ _
  · filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (⌈x^2⌉₊)] with n hn
    have hle : x^2 ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    exact (min_eq_left (by linarith : x^2 ≤ (n:ℝ)+1)).symm

private theorem recover_second_moment {E : ℝ → ℝ} {B : ℕ → ℝ → ℝ}
    {m : ℕ → ℝ} {S C : ℝ}
    (hlim : ∀ n, Tendsto (B n) atTop (𝓝 (m n))) (hm : Tendsto m atTop (𝓝 S))
    (herr : ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      B n T ≤ E T ∧ E T ≤ B n T + C/((n:ℝ)+1)) :
    Tendsto E atTop (𝓝 S) := by
  have hden : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => C/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨n,hn⟩ := (hm.eventually (lt_mem_nhds ha)).exists
    filter_upwards [(hlim n).eventually (lt_mem_nhds hn),herr] with t hl he
    exact hl.trans_le (he n).1
  · intro b hb
    have hu := hm.add hsmall
    simp only [add_zero] at hu
    obtain ⟨n,hn⟩ := (hu.eventually (gt_mem_nhds hb)).exists
    have ht := (hlim n).add_const (C/((n:ℝ)+1))
    filter_upwards [ht.eventually (gt_mem_nhds hn),herr] with t hl he
    exact (he n).2.trans_lt hl

/-- After fixing the width, the finite zero cutoff introduces no error at the
bottom endpoint for all sufficiently large heights. -/
theorem eventually_window_energy_eq_count_square (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, unfoldedWindowEnergy T q =
      (∫ t : ℝ, (actualWindowCount T (q/(Real.log T/(2*Real.pi))) t)^2)/T := by
  obtain ⟨d,hd,hfloor⟩ := exists_ordinate_floor
  have hw : Tendsto (fun T : ℝ => q/(Real.log T/(2*Real.pi))) atTop (𝓝 0) := by
    simp_rw [div_div_eq_mul_div]
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (q*(2*Real.pi))
  filter_upwards [hw.eventually (gt_mem_nhds hd)] with T hT
  rw [integral_actualWindowCount_sq T _ (fun c => hT.le.trans (hfloor T c))]
  rfl

theorem window_energy_of_weak_count_limit {q : ℝ} {ν : Measure ℝ}
    (hw : WindowCountWeakLimit q ν) (hf : BoundedTranslatedFourthMoment q)
    (hν : Integrable (fun x : ℝ => x^2) ν) :
    Tendsto (fun T => unfoldedWindowEnergy T q) atTop (𝓝 (∫ x, x^2 ∂ν)) := by
  let K (T : ℝ) := actualWindowCount T (q/(Real.log T/(2*Real.pi)))
  let cap (n : ℕ) (x : ℝ) := min (x^2) ((n:ℝ)+1)
  let B (n : ℕ) (T : ℝ) := (∫ t : ℝ, cap n (K T t))/T
  let m (n : ℕ) := ∫ x, cap n x ∂ν
  have hB (n : ℕ) : Tendsto (B n) atTop (𝓝 (m n)) := by
    apply hw.2 (cap n) (by dsimp [cap]; fun_prop) (by simp [cap] <;> positivity)
    refine ⟨(n:ℝ)+1,fun x => ?_⟩
    rw [abs_of_nonneg (show 0 ≤ cap n x by exact le_min (sq_nonneg _) (by positivity))]
    exact min_le_right _ _
  obtain ⟨C,_,hC⟩ := hf
  have he : ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      B n T ≤ (∫ t : ℝ, (K T t)^2)/T ∧
      (∫ t : ℝ, (K T t)^2)/T ≤ B n T + C/((n:ℝ)+1) := by
    filter_upwards [hC,eventually_gt_atTop (0:ℝ)] with T hF hT
    intro n
    have hn : 0 < (n:ℝ)+1 := by positivity
    obtain ⟨hl,hu⟩ := cap_second_error (actual_count_measurable T (q/(Real.log T/(2*Real.pi))))
      (windowCount_sq_integrable _ _ _ _) (actual_fourth_integrable T _) hn
    have hh : (∫ t : ℝ, (K T t)^2)/T ≤ ((∫ t : ℝ, cap n (K T t)) +
        (∫ t : ℝ, (K T t)^4)/((n:ℝ)+1))/T := div_le_div_of_nonneg_right hu hT.le
    rw [add_div, div_right_comm (∫ t : ℝ, (K T t)^4) _ T] at hh
    exact ⟨div_le_div_of_nonneg_right hl hT.le,
      hh.trans (add_le_add_right (div_le_div_of_nonneg_right hF hn.le) _)⟩
  exact (recover_second_moment hB (model_capped_square_limit ν hν) he).congr'
    ((eventually_window_energy_eq_count_square q).mono fun _ h => h.symm)

/-- Single-interval count laws at all positive rational widths suffice for
the ordinary two-point law and density-one simplicity and criticality. -/
theorem pcc_and_simple_density_of_weak_count_laws
    (hf : ∀ q : ℚ, 0 < q → BoundedTranslatedFourthMoment q)
    (hlaw : ∀ q : ℚ, 0 < q → ∃ ν : Measure ℝ,
      WindowCountWeakLimit q ν ∧ Integrable (fun x : ℝ => x^2) ν ∧
      (∫ x, x^2 ∂ν) = sineWindowEnergy q) :
    PositiveGapPCC ∧
      Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  have hV : RationalSineWindowVariance := by
    intro q hq
    obtain ⟨ν,hw,hν,h2⟩ := hlaw q hq
    apply (unfoldedWindowVariance_tendsto_iff (by exact_mod_cast hq.le : 0 ≤ (q:ℝ))).mpr
    rw [← h2]
    exact window_energy_of_weak_count_limit hw (hf q hq) hν
  exact ⟨positiveGapPCC_of_rationalSineWindowVariance hV,
    (density_one_of_rationalSineWindowVariance hV).1⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
