import RiemannResearch.Analysis.CrossCorrelationDerivative
import RiemannResearch.RH.NymanCompletionAdmissibility

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Closure of the actual smooth-superexponential test class under correlation

Every derivative of the correlation is identified with an actual correlation
of a differentiated input. Differentiability of this complete tower supplies
C-infinity regularity. Real projection retains the same decay bounds.
-/

open MeasureTheory

namespace RiemannResearch.Analysis

theorem SmoothSuperexponentialDecay.iteratedDeriv {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (j : ℕ) :
    SmoothSuperexponentialDecay (_root_.iteratedDeriv j f) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem SmoothSuperexponentialDecay.iteratedDeriv_crossCorrelation {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) (j : ℕ) :
    _root_.iteratedDeriv j (RiemannResearch.Analysis.crossCorrelation f g) =
      RiemannResearch.Analysis.crossCorrelation (_root_.iteratedDeriv j f) g := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
      have hj := hf.iteratedDeriv j
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      exact hj.decay.deriv_crossCorrelation hg.decay hj.deriv.decay
        (hj.1.differentiable (by simp)) hj.deriv.1.continuous hg.1.continuous

theorem SmoothSuperexponentialDecay.crossCorrelation {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) :
    SmoothSuperexponentialDecay (RiemannResearch.Analysis.crossCorrelation f g) := by
  constructor
  · apply contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞))
    intro j _
    rw [hf.iteratedDeriv_crossCorrelation hg j]
    have hj := hf.iteratedDeriv j
    intro t
    exact (hj.decay.hasDerivAt_crossCorrelation hg.decay hj.deriv.decay
      (hj.1.differentiable (by simp)) hj.deriv.1.continuous hg.1.continuous t).differentiableAt
  · intro j
    rw [hf.iteratedDeriv_crossCorrelation hg j]
    exact (hf.iteratedDeriv j).decay.crossCorrelation hg.decay
      (hf.iteratedDeriv j).1.continuous hg.1.continuous

private noncomputable def realProjectionCLM : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM

theorem deriv_realPartEmbedding {f : ℝ → ℂ} (hfd : Differentiable ℝ f) :
    deriv (fun y => ((f y).re : ℂ)) = fun y => ((deriv f y).re : ℂ) := by
  funext y
  have h := realProjectionCLM.hasFDerivAt.comp_hasDerivAt y (hfd y).hasDerivAt
  convert h.deriv using 1 <;> rfl

theorem SmoothSuperexponentialDecay.iteratedDeriv_realPartEmbedding {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (j : ℕ) :
    _root_.iteratedDeriv j (fun y => ((f y).re : ℂ)) =
      fun y => ((_root_.iteratedDeriv j f y).re : ℂ) := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      exact deriv_realPartEmbedding ((hf.iteratedDeriv j).1.differentiable (by simp))

theorem SmoothSuperexponentialDecay.realPartEmbedding {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) :
    SmoothSuperexponentialDecay (fun y => ((f y).re : ℂ)) := by
  constructor
  · exact realProjectionCLM.contDiff.comp hf.1
  · intro j
    rw [hf.iteratedDeriv_realPartEmbedding j]
    intro a ha
    obtain ⟨C, hC, hbound⟩ := hf.2 j a ha
    refine ⟨C, hC, fun y => ?_⟩
    calc
      ‖((_root_.iteratedDeriv j f y).re : ℂ)‖ = |(_root_.iteratedDeriv j f y).re| := by simp
      _ ≤ ‖_root_.iteratedDeriv j f y‖ := Complex.abs_re_le_norm _
      _ ≤ C * Real.exp (-a * |y|) := hbound y

end RiemannResearch.Analysis
