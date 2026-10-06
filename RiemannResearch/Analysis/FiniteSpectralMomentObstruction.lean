import RiemannResearch.Analysis.FiniteSpectralEscape
import RiemannResearch.Analysis.FiniteSpectralDoubleLog

/-!
# Quantitative obstruction for complete-source moment budgets

This converts the exact escape theorem into an eventual lower floor, without
assuming that the normalized moment has a limit. The finite moment contains
every source component, including all discarded high eigenvalues.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

variable {ι : Type*}

/-- At every admissible moving cutoff, the complete moment normalized by its
threshold value has limiting lower floor at least the residual defect. -/
theorem eventually_lt_normalized_moment_of_moving_escape
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta : ℝ)
    (R : ℕ → ℝ) (Phi : ℕ → ℝ → ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hR : ∀ n, 1 ≤ R n)
    (hPhiR : ∀ n, 0 < Phi n (R n))
    (hPhi : ∀ n i, i ∈ s n → 0 ≤ Phi n (lam n i))
    (hmono : ∀ n i, i ∈ s n → R n ≤ lam n i →
      Phi n (R n) ≤ Phi n (lam n i))
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hlow : Tendsto (fun n =>
      (1 + R n) * optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0)) :
    ∀ c : ℝ, c < delta → ∀ᶠ n in atTop,
      c < moment (s n) (w n) (lam n) (Phi n) / Phi n (R n) := by
  have hB := moving_highMass_tendsto_of_correction_and_low_budget
    s w lam delta R hw hlam hR hT hlow
  intro c hc
  filter_upwards [hB.eventually_const_lt hc] with n hn
  apply hn.trans_le
  apply (le_div_iff₀ (hPhiR n)).mpr
  rw [mul_comm]
  exact threshold_mul_highMass_le_moment
    (s n) (w n) (lam n) (R n) (Phi n) (hw n) (hPhi n) (hmono n)

/-- If a normalized moment does converge, its limit cannot be smaller than
the residual defect. This is stronger information than the zero consumer. -/
theorem defect_le_normalized_moment_limit
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta L : ℝ)
    (R : ℕ → ℝ) (Phi : ℕ → ℝ → ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hR : ∀ n, 1 ≤ R n)
    (hPhiR : ∀ n, 0 < Phi n (R n))
    (hPhi : ∀ n i, i ∈ s n → 0 ≤ Phi n (lam n i))
    (hmono : ∀ n i, i ∈ s n → R n ≤ lam n i →
      Phi n (R n) ≤ Phi n (lam n i))
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hlow : Tendsto (fun n =>
      (1 + R n) * optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0))
    (hM : Tendsto (fun n => moment (s n) (w n) (lam n) (Phi n) /
      Phi n (R n)) atTop (𝓝 L)) : delta ≤ L := by
  apply le_of_tendsto_of_tendsto
    (moving_highMass_tendsto_of_correction_and_low_budget
      s w lam delta R hw hlam hR hT hlow) hM
  apply Filter.Eventually.of_forall
  intro n
  apply (le_div_iff₀ (hPhiR n)).mpr
  rw [mul_comm]
  exact threshold_mul_highMass_le_moment
    (s n) (w n) (lam n) (R n) (Phi n) (hw n) (hPhi n) (hmono n)

/-- General denominator normalization. Only the threshold/denominator ratio
must tend to one; the moment itself may fail to have any limit. -/
theorem eventually_lt_normalized_moment_of_scale_ratio
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta : ℝ)
    (R b : ℕ → ℝ) (Phi : ℕ → ℝ → ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hR : ∀ n, 1 ≤ R n) (hb : ∀ n, 0 < b n)
    (hPhi : ∀ n i, i ∈ s n → 0 ≤ Phi n (lam n i))
    (hmono : ∀ n i, i ∈ s n → R n ≤ lam n i →
      Phi n (R n) ≤ Phi n (lam n i))
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hlow : Tendsto (fun n =>
      (1 + R n) * optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0))
    (hscale : Tendsto (fun n => Phi n (R n) / b n) atTop (𝓝 1)) :
    ∀ c : ℝ, c < delta → ∀ᶠ n in atTop,
      c < moment (s n) (w n) (lam n) (Phi n) / b n := by
  have hB := moving_highMass_tendsto_of_correction_and_low_budget
    s w lam delta R hw hlam hR hT hlow
  have hprod : Tendsto (fun n => (Phi n (R n) / b n) *
      highMass (s n) (w n) (lam n) (R n)) atTop (𝓝 delta) := by
    simpa only [one_mul] using hscale.mul hB
  intro c hc
  filter_upwards [hprod.eventually_const_lt hc] with n hn
  apply hn.trans_le
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right
    (threshold_mul_highMass_le_moment
      (s n) (w n) (lam n) (R n) (Phi n) (hw n) (hPhi n) (hmono n)) (hb n).le

/-- The square-root cutoff loses only an additive log 2 on the exact outer
logarithmic scale. The previous factor-two lower estimate is not sharp. -/
theorem relative_doubleLog_scale_sub_log_two_le_cutoff
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigma_one : sigma < 1) :
    Real.log (1 + Real.log (1 / sigma)) - Real.log 2 ≤
      doubleLog (1 / Real.sqrt sigma) := by
  have hsqrt : 0 < Real.sqrt sigma := Real.sqrt_pos.mpr hsigma
  have hsqrt_ne : Real.sqrt sigma ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt sigma) ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have hlog_sigma : Real.log sigma = 2 * Real.log (Real.sqrt sigma) := by
    calc
      Real.log sigma = Real.log (Real.sqrt sigma * Real.sqrt sigma) := by
        rw [← pow_two, hsqrt_sq]
      _ = Real.log (Real.sqrt sigma) + Real.log (Real.sqrt sigma) :=
        Real.log_mul hsqrt_ne hsqrt_ne
      _ = 2 * Real.log (Real.sqrt sigma) := by ring
  have hlog_inv_sigma : Real.log (1 / sigma) = -Real.log sigma := by
    simpa only [one_div] using Real.log_inv sigma
  have hlog_inv_sqrt : Real.log (1 / Real.sqrt sigma) =
      Real.log (1 / sigma) / 2 := by
    have hroot : Real.log (1 / Real.sqrt sigma) = -Real.log (Real.sqrt sigma) := by
      simpa only [one_div] using Real.log_inv (Real.sqrt sigma)
    rw [hroot, hlog_inv_sigma]
    linarith [hlog_sigma]
  have hL : 0 < Real.log (1 / sigma) :=
    Real.log_pos ((lt_div_iff₀ hsigma).mpr (by linarith))
  have hhalf : Real.log (1 / sigma) / 2 ≤
      Real.log (1 + 1 / Real.sqrt sigma) := by
    rw [← hlog_inv_sqrt]
    exact Real.log_le_log (one_div_pos.mpr hsqrt) (by linarith)
  calc
    Real.log (1 + Real.log (1 / sigma)) - Real.log 2 =
        Real.log ((1 + Real.log (1 / sigma)) / 2) := by
      rw [Real.log_div (by linarith : 1 + Real.log (1 / sigma) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ Real.log (1 + Real.log (1 / sigma) / 2) :=
      Real.log_le_log (by positivity) (by linarith)
    _ ≤ doubleLog (1 / Real.sqrt sigma) := by
      unfold doubleLog
      exact Real.log_le_log (by linarith) (by linarith)

/-- A sharp finite envelope with only the additive log 2 loss. Its coefficient
relative to the original outer-log scale tends to one as sigma tends to zero. -/
theorem correction_le_relative_doubleLog_sharp_envelope
    (s : Finset ι) (w lam : ι → ℝ) (sigma : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hscale : Real.log 2 < Real.log (1 + Real.log (1 / sigma)))
    (htail : optimizerTail s w lam ≤ sigma) :
    correction s w lam ≤ sigma + Real.sqrt sigma +
      moment s w lam doubleLog /
        (Real.log (1 + Real.log (1 / sigma)) - Real.log 2) := by
  have hsqrt : 0 < Real.sqrt sigma := Real.sqrt_pos.mpr hsigma
  have hsqrt_ne : Real.sqrt sigma ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt sigma) ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have hlow : (1 + 1 / Real.sqrt sigma) * optimizerTail s w lam ≤
      sigma + Real.sqrt sigma := by
    have hfactor : 0 ≤ 1 + 1 / Real.sqrt sigma := by positivity
    have hmul := mul_le_mul_of_nonneg_left htail hfactor
    have heq : (1 + 1 / Real.sqrt sigma) * sigma = sigma + Real.sqrt sigma := by
      field_simp [hsqrt_ne]
      nlinarith [hsqrt_sq]
    exact hmul.trans_eq heq
  have hM : 0 ≤ moment s w lam doubleLog := by
    unfold moment
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (doubleLog_nonneg (hlam i hi))
  have hquot : moment s w lam doubleLog / doubleLog (1 / Real.sqrt sigma) ≤
      moment s w lam doubleLog /
        (Real.log (1 + Real.log (1 / sigma)) - Real.log 2) :=
    div_le_div_of_nonneg_left hM (sub_pos.mpr hscale)
      (relative_doubleLog_scale_sub_log_two_le_cutoff sigma hsigma hsigma_one)
  exact (correction_le_threshold_tail_add_doubleLog_moment
    s w lam (1 / Real.sqrt sigma) hw hlam (one_div_pos.mpr hsqrt)).trans
    (add_le_add hlow hquot)

/-- The complete double-logarithmic moment has normalized limiting lower
floor delta, with coefficient one. No limit of the moment is assumed.
The chosen positive envelope need not equal the physical optimizer tail. -/
theorem eventually_lt_relative_doubleLog_moment_of_envelope
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta : ℝ) (sigma : ℕ → ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ n, 0 < sigma n) (hone : ∀ n, sigma n < 1)
    (htail : ∀ n, optimizerTail (s n) (w n) (lam n) ≤ sigma n) :
    ∀ c : ℝ, c < delta → ∀ᶠ n in atTop,
      c < moment (s n) (w n) (lam n) doubleLog /
        Real.log (1 + Real.log (1 / sigma n)) := by
  let R : ℕ → ℝ := fun n => 1 / Real.sqrt (sigma n)
  let D : ℕ → ℝ := fun n => Real.log (1 + Real.log (1 / sigma n))
  have hR : ∀ n, 1 ≤ R n := by
    intro n
    have hroot : 0 < Real.sqrt (sigma n) := Real.sqrt_pos.mpr (hpos n)
    apply (le_div_iff₀ hroot).mpr
    have hsquare := Real.sq_sqrt (hpos n).le
    have hrootnonneg := Real.sqrt_nonneg (sigma n)
    nlinarith [hone n]
  have hD : ∀ n, 0 < D n := by
    intro n
    have hinv : 1 < 1 / sigma n := (lt_div_iff₀ (hpos n)).mpr (by linarith [hone n])
    exact Real.log_pos (by linarith [Real.log_pos hinv])
  have hsqrt : Tendsto (fun n => Real.sqrt (sigma n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsigma
  have hmajor : Tendsto (fun n => sigma n + Real.sqrt (sigma n)) atTop (𝓝 0) := by
    simpa only [add_zero] using hsigma.add hsqrt
  have hlow : Tendsto (fun n => (1 + R n) *
      optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => mul_nonneg (by linarith [hR n])
        (optimizerTail_nonneg (s n) (w n) (lam n) (hw n) (hlam n)))
      _ hmajor
    intro n
    have hroot : 0 < Real.sqrt (sigma n) := Real.sqrt_pos.mpr (hpos n)
    have hrootne : Real.sqrt (sigma n) ≠ 0 := ne_of_gt hroot
    have hsquare : (Real.sqrt (sigma n)) ^ 2 = sigma n := Real.sq_sqrt (hpos n).le
    have hmul := mul_le_mul_of_nonneg_left (htail n)
      (show 0 ≤ 1 + R n by linarith [hR n])
    have hid : (1 + R n) * sigma n = sigma n + Real.sqrt (sigma n) := by
      dsimp [R]
      field_simp [hrootne]
      nlinarith [hsquare]
    exact hmul.trans_eq hid
  have hB := moving_highMass_tendsto_of_correction_and_low_budget
    s w lam delta R hw hlam hR hT hlow
  have hinv : Tendsto (fun n => 1 / sigma n) atTop atTop := by
    have hwithin : Tendsto sigma atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hsigma, Filter.Eventually.of_forall hpos⟩
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hwithin
  have hL : Tendsto (fun n => Real.log (1 / sigma n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hinv
  have hinner : Tendsto (fun n => 1 + Real.log (1 / sigma n)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hL.eventually (eventually_ge_atTop (b - 1))] with n hn
    linarith
  have hDto : Tendsto D atTop atTop := Real.tendsto_log_atTop.comp hinner
  have hquot : Tendsto (fun n => Real.log 2 / D n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hDto
  have hscale : Tendsto (fun n => (D n - Real.log 2) / D n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hquot
    simp only [sub_zero] at h
    convert h using 1
    ext n
    field_simp [ne_of_gt (hD n)]
  have hprod : Tendsto (fun n => ((D n - Real.log 2) / D n) *
      highMass (s n) (w n) (lam n) (R n)) atTop (𝓝 delta) := by
    simpa only [one_mul] using hscale.mul hB
  intro c hc
  filter_upwards [hprod.eventually_const_lt hc] with n hn
  apply hn.trans_le
  have hmark := threshold_mul_highMass_le_moment
    (s n) (w n) (lam n) (R n) doubleLog (hw n)
    (fun i hi => doubleLog_nonneg (hlam n i hi))
    (fun i hi hRi => doubleLog_mono_nonneg (by linarith [hR n]) hRi)
  have hscalele : D n - Real.log 2 ≤ doubleLog (R n) :=
    relative_doubleLog_scale_sub_log_two_le_cutoff (sigma n) (hpos n) (hone n)
  have hBnonneg := highMass_nonneg (s n) (w n) (lam n) (R n) (hw n)
  have hnum := (mul_le_mul_of_nonneg_right hscalele hBnonneg).trans hmark
  dsimp [D] at hnum ⊢
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hnum (hD n).le

/-- Any strict feedback fraction of the actual correction is absorbable on
the coefficient-one normalized double-log scale. The moment need not vanish
before this argument: the limiting defect forces its lower floor to delta. -/
theorem defect_eq_zero_of_relative_doubleLog_feedback
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta theta : ℝ)
    (sigma E : ℕ → ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ n, 0 < sigma n) (hone : ∀ n, sigma n < 1)
    (htail : ∀ n, optimizerTail (s n) (w n) (lam n) ≤ sigma n)
    (htheta : theta < 1) (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ᶠ n in atTop,
      moment (s n) (w n) (lam n) doubleLog /
          Real.log (1 + Real.log (1 / sigma n)) ≤
        E n + theta * correction (s n) (w n) (lam n)) : delta = 0 := by
  have hdelta : 0 ≤ delta := le_of_tendsto_of_tendsto tendsto_const_nhds hT
    (Filter.Eventually.of_forall fun n =>
      correction_nonneg (s n) (w n) (lam n) (hw n) (hlam n))
  by_contra hne
  have hdelta_pos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
  have hstrict : theta * delta < delta := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta hdelta_pos
  let c : ℝ := (delta + theta * delta) / 2
  have hc_delta : c < delta := by dsimp [c]; linarith
  have htheta_c : theta * delta < c := by dsimp [c]; linarith
  have hlower := eventually_lt_relative_doubleLog_moment_of_envelope
    s w lam delta sigma hw hlam hT hsigma hpos hone htail c hc_delta
  have hrhs : Tendsto (fun n => E n + theta * correction (s n) (w n) (lam n))
      atTop (𝓝 (theta * delta)) := by
    simpa only [zero_add] using hE.add (hT.const_mul theta)
  obtain ⟨n, hn⟩ := (hlower.and (hbudget.and (hrhs.eventually_lt_const htheta_c))).exists
  linarith [hn.1, hn.2.1, hn.2.2]

end RiemannResearch.Analysis.FiniteSpectralBudget
