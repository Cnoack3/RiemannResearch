import RiemannResearch.Analysis.FiniteSpectralRelativeLog

/-!
# Relative double logarithmic source budgets

The function `doubleLog x = log (1 + log (1 + x))` grows more slowly
than the logarithmic moment.  The actual Pareto source realization and
arithmetic budget remain separate obligations.

Source: user-provided Green-Pareto-Schur continuation, Sections 17 and 20,
supporting the moment-threshold strategy. The double logarithmic
specialization is developed here without a mathematical-priority claim.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

def doubleLog (x : ℝ) : ℝ := Real.log (1 + Real.log (1 + x))

theorem doubleLog_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ doubleLog x := by
  unfold doubleLog
  exact Real.log_nonneg (by linarith [Real.log_nonneg (by linarith : 1 ≤ 1 + x)])

theorem doubleLog_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    doubleLog x ≤ doubleLog y := by
  unfold doubleLog
  have hinner : Real.log (1 + x) ≤ Real.log (1 + y) :=
    Real.log_le_log (by linarith) (by linarith)
  exact Real.log_le_log
    (by linarith [Real.log_nonneg (by linarith : 1 ≤ 1 + x)])
    (by linarith)

/-- Concavity of the outer logarithm retains half of the inner scale. -/
theorem log_one_add_half_le_two_log {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) / 2 ≤ Real.log (1 + x / 2) := by
  have hp : 0 < 1 + x / 2 := by linarith
  have hsquare : 1 + x ≤ (1 + x / 2) * (1 + x / 2) := by
    nlinarith [sq_nonneg x]
  have h := Real.log_le_log (by linarith : 0 < 1 + x) hsquare
  rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hp)] at h
  linarith

/-- The same square-root cutoff controls the double logarithmic scale. -/
theorem half_relative_doubleLog_le_cutoff (sigma : ℝ)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1) :
    Real.log (1 + Real.log (1 / sigma)) / 2 ≤
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
  have hhalf : Real.log (1 / sigma) / 2 ≤
      Real.log (1 + 1 / Real.sqrt sigma) := by
    rw [← hlog_inv_sqrt]
    exact Real.log_le_log (one_div_pos.mpr hsqrt) (by linarith)
  have hinv : 1 < 1 / sigma := (lt_div_iff₀ hsigma).mpr (by linarith)
  have hlog_pos : 0 < Real.log (1 / sigma) := Real.log_pos hinv
  apply (log_one_add_half_le_two_log hlog_pos.le).trans
  unfold doubleLog
  exact Real.log_le_log (by linarith) (by linarith)

/-- The finite source bound uses the complete double logarithmic moment. -/
theorem correction_le_threshold_tail_add_doubleLog_moment
    {iota : Type*} (s : Finset iota) (w lam : iota → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hR : 0 < R) :
    correction s w lam ≤ (1 + R) * optimizerTail s w lam +
      moment s w lam doubleLog / doubleLog R := by
  apply correction_le_threshold_tail_add_local_moment_quotient
    s w lam R doubleLog hw hlam hR.le
  · unfold doubleLog
    exact Real.log_pos (by linarith [Real.log_pos (by linarith : 1 < 1 + R)])
  · intro i hi
    exact doubleLog_nonneg (hlam i hi)
  · intro i hi hRi
    exact doubleLog_mono_nonneg hR.le hRi

/-- Double logarithmic moments may grow faster than bounded moments, and
the logarithmic moment itself need not meet the old relative-log budget. -/
theorem correction_le_relative_doubleLog_envelope
    {iota : Type*} (s : Finset iota) (w lam : iota → ℝ) (sigma : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (htail : optimizerTail s w lam ≤ sigma) :
    correction s w lam ≤ sigma + Real.sqrt sigma +
      2 * moment s w lam doubleLog / Real.log (1 + Real.log (1 / sigma)) := by
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
  have hinv : 1 < 1 / sigma := (lt_div_iff₀ hsigma).mpr (by linarith)
  have hlog_pos : 0 < Real.log (1 / sigma) := Real.log_pos hinv
  have hdouble_pos : 0 < Real.log (1 + Real.log (1 / sigma)) :=
    Real.log_pos (by linarith)
  have hhalf := half_relative_doubleLog_le_cutoff sigma hsigma hsigma_one
  have hquot : moment s w lam doubleLog / doubleLog (1 / Real.sqrt sigma) ≤
      2 * moment s w lam doubleLog / Real.log (1 + Real.log (1 / sigma)) := by
    calc
      _ ≤ moment s w lam doubleLog / (Real.log (1 + Real.log (1 / sigma)) / 2) :=
        div_le_div_of_nonneg_left hM (by linarith) hhalf
      _ = 2 * moment s w lam doubleLog / Real.log (1 + Real.log (1 / sigma)) := by
        field_simp [ne_of_gt hdouble_pos]
  exact (correction_le_threshold_tail_add_doubleLog_moment
    s w lam (1 / Real.sqrt sigma) hw hlam (one_div_pos.mpr hsqrt)).trans
    (add_le_add hlow hquot)

/-- An unbounded double logarithmic moment is sufficient when its relative
scale tends to zero cofinally.  The conclusion is the limiting defect zero;
the actual spectrum realization and arithmetic provider are not assumed proved. -/
theorem limit_eq_zero_of_cofinal_relative_doubleLog_envelope
    {iota : Type*} (s : ℕ → Finset iota) (w lam : ℕ → iota → ℝ)
    (sigma : ℕ → ℝ) (k : ℕ → ℕ) (delta : ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hk : Tendsto k atTop atTop)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (henvelope : ∀ᶠ n in atTop, 0 < sigma n ∧ sigma n < 1 ∧
      optimizerTail (s (k n)) (w (k n)) (lam (k n)) ≤ sigma n)
    (hdoubleLogratio : Tendsto (fun n =>
      moment (s (k n)) (w (k n)) (lam (k n)) doubleLog /
        Real.log (1 + Real.log (1 / sigma n))) atTop (𝓝 0)) : delta = 0 := by
  have hsqrt : Tendsto (fun n => Real.sqrt (sigma n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsigma
  have hrhs : Tendsto (fun n => sigma n + Real.sqrt (sigma n) +
      2 * (moment (s (k n)) (w (k n)) (lam (k n)) doubleLog /
        Real.log (1 + Real.log (1 / sigma n)))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      (hsigma.add hsqrt).add (hdoubleLogratio.const_mul 2)
  have hbudget : ∀ᶠ n in atTop,
      correction (s (k n)) (w (k n)) (lam (k n)) ≤
      sigma n + Real.sqrt (sigma n) +
        2 * (moment (s (k n)) (w (k n)) (lam (k n)) doubleLog /
          Real.log (1 + Real.log (1 / sigma n))) := by
    filter_upwards [henvelope] with n hn
    simpa only [mul_div_assoc] using correction_le_relative_doubleLog_envelope
      (s (k n)) (w (k n)) (lam (k n)) (sigma n)
      (hw (k n)) (hlam (k n)) hn.1 hn.2.1 hn.2.2
  have hdelta_le : delta ≤ 0 :=
    le_of_tendsto_of_tendsto (hT.comp hk) hrhs hbudget
  have hdelta_nonneg : 0 ≤ delta :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hT
      (Filter.Eventually.of_forall fun n =>
        correction_nonneg (s n) (w n) (lam n) (hw n) (hlam n))
  exact le_antisymm hdelta_le hdelta_nonneg

end RiemannResearch.Analysis.FiniteSpectralBudget
