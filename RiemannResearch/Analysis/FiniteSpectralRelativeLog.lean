import RiemannResearch.Analysis.FiniteSpectralBudget
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Relative logarithmic source budgets

Source: the Green--Pareto--Schur continuation, Section 12.  This module
formalizes the literal normalized-logarithmic provider.  It permits a
positive envelope sigma for the optimizer tail; therefore no positivity
assumption on the optimizer tail itself is needed.

The arithmetic moment estimate and a realization of the spectral data as
the actual Pareto matrices remain separate hypotheses.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

/-- The cutoff `1 / sqrt sigma` converts a logarithmic spectral estimate
into an explicit bound normalized by `log (1 / sigma)`. -/
theorem relative_log_scalar_bound (T S L sigma : ℝ)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hSsigma : S ≤ sigma) (hL : 0 ≤ L)
    (hbudget : T ≤ (1 + 1 / Real.sqrt sigma) * S +
      L / Real.log (1 + 1 / Real.sqrt sigma)) :
    T ≤ sigma + Real.sqrt sigma + 2 * L / Real.log (1 / sigma) := by
  have hsqrt : 0 < Real.sqrt sigma := Real.sqrt_pos.mpr hsigma
  have hsqrt_ne : Real.sqrt sigma ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt sigma) ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have hlow : (1 + 1 / Real.sqrt sigma) * S ≤ sigma + Real.sqrt sigma := by
    have hfactor : 0 ≤ 1 + 1 / Real.sqrt sigma := by positivity
    have hmul := mul_le_mul_of_nonneg_left hSsigma hfactor
    have heq : (1 + 1 / Real.sqrt sigma) * sigma = sigma + Real.sqrt sigma := by
      field_simp [hsqrt_ne]
      nlinarith [hsqrt_sq]
    exact hmul.trans_eq heq
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
  have hquot : L / Real.log (1 + 1 / Real.sqrt sigma) ≤
      2 * L / Real.log (1 / sigma) := by
    calc
      _ ≤ L / (Real.log (1 / sigma) / 2) :=
        div_le_div_of_nonneg_left hL (by linarith) hhalf
      _ = 2 * L / Real.log (1 / sigma) := by
        field_simp [ne_of_gt hlog_pos]
  exact hbudget.trans (add_le_add hlow hquot)

/-- Literal relative-log finite bound, allowing a positive envelope larger
than the actual optimizer tail.  Every source component is retained. -/
theorem correction_le_relative_log_envelope
    {iota : Type*} (s : Finset iota) (w lam : iota → ℝ) (sigma : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (htail : optimizerTail s w lam ≤ sigma) :
    correction s w lam ≤ sigma + Real.sqrt sigma +
      2 * (∑ i ∈ s, w i * Real.log (1 + lam i)) / Real.log (1 / sigma) := by
  apply relative_log_scalar_bound
    (correction s w lam) (optimizerTail s w lam)
    (∑ i ∈ s, w i * Real.log (1 + lam i)) sigma
    hsigma hsigma_one htail
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (Real.log_nonneg (by linarith [hlam i hi]))
  · exact correction_le_threshold_tail_add_log_moment s w lam
      (1 / Real.sqrt sigma) hw hlam (one_div_pos.mpr (Real.sqrt_pos.mpr hsigma))

/-- An unbounded source log moment is permissible provided that its ratio
to the logarithm of the reciprocal optimizer-tail envelope tends to zero
along a cofinal sequence.  No arithmetic provider is asserted. -/
theorem limit_eq_zero_of_cofinal_relative_log_envelope
    {iota : Type*} (s : ℕ → Finset iota) (w lam : ℕ → iota → ℝ)
    (sigma : ℕ → ℝ) (k : ℕ → ℕ) (delta : ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hk : Tendsto k atTop atTop)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (henvelope : ∀ᶠ n in atTop, 0 < sigma n ∧ sigma n < 1 ∧
      optimizerTail (s (k n)) (w (k n)) (lam (k n)) ≤ sigma n)
    (hlogratio : Tendsto (fun n =>
      (∑ i ∈ s (k n), w (k n) i * Real.log (1 + lam (k n) i)) /
        Real.log (1 / sigma n)) atTop (𝓝 0)) : delta = 0 := by
  have hsqrt : Tendsto (fun n => Real.sqrt (sigma n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsigma
  have hrhs : Tendsto (fun n => sigma n + Real.sqrt (sigma n) +
      2 * ((∑ i ∈ s (k n), w (k n) i * Real.log (1 + lam (k n) i)) /
        Real.log (1 / sigma n))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hsigma.add hsqrt).add (hlogratio.const_mul 2)
  have hbudget : ∀ᶠ n in atTop,
      correction (s (k n)) (w (k n)) (lam (k n)) ≤
      sigma n + Real.sqrt (sigma n) +
        2 * ((∑ i ∈ s (k n), w (k n) i * Real.log (1 + lam (k n) i)) /
          Real.log (1 / sigma n)) := by
    filter_upwards [henvelope] with n hn
    have h := correction_le_relative_log_envelope
      (s (k n)) (w (k n)) (lam (k n)) (sigma n)
      (hw (k n)) (hlam (k n)) hn.1 hn.2.1 hn.2.2
    simpa only [mul_div_assoc] using h
  have hdelta_le : delta ≤ 0 :=
    le_of_tendsto_of_tendsto (hT.comp hk) hrhs hbudget
  have hdelta_nonneg : 0 ≤ delta :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hT
      (Filter.Eventually.of_forall fun n =>
        correction_nonneg (s n) (w n) (lam n) (hw n) (hlam n))
  exact le_antisymm hdelta_le hdelta_nonneg

end RiemannResearch.Analysis.FiniteSpectralBudget
