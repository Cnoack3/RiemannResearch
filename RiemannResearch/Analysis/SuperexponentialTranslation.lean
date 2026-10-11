import RiemannResearch.Analysis.SmoothSuperexponentialDecay

/-!
# Translation of the smooth superexponential test class

Elementary translation closure, used by the actual Weil reflection kernel.
The smooth class is defined in `Analysis.SmoothSuperexponentialDecay`.
Source: direct proof from the decay definition and the derivative chain rule.
-/

noncomputable section

namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.translate {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (t : ℝ) :
    SuperexponentialDecay (fun x => f (x - t)) := by
  intro a ha
  obtain ⟨C, hC, hCf⟩ := hf a ha
  refine ⟨C * Real.exp (a * |t|), by positivity, ?_⟩
  intro x
  have hx : |x| ≤ |x - t| + |t| := by
    simpa only [sub_add_cancel] using abs_add_le (x - t) t
  calc
    ‖f (x - t)‖ ≤ C * Real.exp (-a * |x - t|) := hCf _
    _ ≤ C * Real.exp (a * |t| + (-a * |x|)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (C * Real.exp (a * |t|)) * Real.exp (-a * |x|) := by
      rw [Real.exp_add]
      ring

theorem deriv_translate_smooth {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (fun x => f (x - t)) = fun x => deriv f (x - t) := by
  funext x
  have hid : HasDerivAt (fun y : ℝ => y - t) 1 x := by
    simpa using (hasDerivAt_id x).sub_const t
  simpa only [one_smul, Function.comp_def] using
    ((hf (x - t)).hasDerivAt.scomp x hid).deriv

theorem SmoothSuperexponentialDecay.translate {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (t : ℝ) :
    SmoothSuperexponentialDecay (fun x => f (x - t)) := by
  refine ⟨hf.1.comp (contDiff_id.sub contDiff_const), ?_⟩
  intro j
  induction j generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hf.decay.translate t
  | succ j ih =>
    rw [iteratedDeriv_succ',
      deriv_translate_smooth (hf.1.differentiable (by simp)) t]
    exact ih hf.deriv

end RiemannResearch.Analysis
