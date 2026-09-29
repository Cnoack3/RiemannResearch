import RiemannResearch.Analysis.SuperexponentialPrimitive
import RiemannResearch.RH.NymanCompletionAdmissibility

/-!
# Removing transform zeros preserves the full smooth Weil test class

Source: independently developed integration/ODE argument, September 29, 2026.
This is an analytic provider for a possible converse Weil criterion. It does
not assert Weil positivity, any arithmetic cancellation bound, or RH.
-/

open MeasureTheory

namespace RiemannResearch.Analysis

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem SuperexponentialDecay.add {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g) :
    SuperexponentialDecay (f + g) := by
  intro a ha
  obtain ⟨C, hC, hCf⟩ := hf a ha
  obtain ⟨D, hD, hDg⟩ := hg a ha
  refine ⟨C + D, by positivity, ?_⟩
  intro x
  exact (norm_add_le _ _).trans (by
    change ‖f x‖ + ‖g x‖ ≤ (C + D) * Real.exp (-a * |x|)
    nlinarith [hCf x, hDg x])

theorem SuperexponentialDecay.const_mul {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (c : ℂ) :
    SuperexponentialDecay (fun x => c * f x) := by
  intro a ha
  obtain ⟨C, hC, hCf⟩ := hf a ha
  refine ⟨(‖c‖ + 1) * C, by positivity, ?_⟩
  intro x
  rw [norm_mul]
  calc
    ‖c‖ * ‖f x‖ ≤ ‖c‖ * (C * Real.exp (-a * |x|)) :=
      mul_le_mul_of_nonneg_left (hCf x) (norm_nonneg _)
    _ ≤ _ := by nlinarith [Real.exp_pos (-a * |x|), norm_nonneg c]

theorem SmoothSuperexponentialDecay.add {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) :
    SmoothSuperexponentialDecay (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro j
  have hj : (j : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le
  have he : iteratedDeriv j (f + g) = iteratedDeriv j f + iteratedDeriv j g := by
    funext x
    exact iteratedDeriv_add ((hf.1.of_le hj).contDiffAt) ((hg.1.of_le hj).contDiffAt)
  rw [he]
  exact (hf.2 j).add (hg.2 j)

theorem SmoothSuperexponentialDecay.const_mul {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (c : ℂ) :
    SmoothSuperexponentialDecay (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, ?_⟩
  intro j
  have he : iteratedDeriv j (fun x => c * f x) = fun x => c * iteratedDeriv j f x := by
    funext x
    exact iteratedDeriv_const_mul_field c f
  rw [he]
  exact (hf.2 j).const_mul c

theorem deriv_exp_mul {f : ℝ → ℂ} (hf : Differentiable ℝ f) (c : ℂ) :
    deriv (fun x : ℝ => Complex.exp (c * (x : ℂ)) * f x) =
      fun x : ℝ => Complex.exp (c * (x : ℂ)) * (c * f x + deriv f x) := by
  funext x
  have he : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
      (c * Complex.exp (c * (x : ℂ))) x := by
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
      convert (Complex.ofRealCLM.hasDerivAt (x := x)) using 1 <;> rfl
    have hlin : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      simpa using hid.const_mul c
    convert hlin.cexp using 1; first | rfl | ring
  have h := (he.mul (hf x).hasDerivAt).deriv
  simp only [Pi.mul_def] at h
  rw [h]
  ring

theorem SmoothSuperexponentialDecay.exp_mul {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (c : ℂ) :
    SmoothSuperexponentialDecay (fun x : ℝ => Complex.exp (c * (x : ℂ)) * f x) := by
  constructor
  · have hfc := hf.1
    have hcast : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (x : ℂ)) :=
      Complex.ofRealCLM.contDiff
    fun_prop
  · intro j
    induction j generalizing f with
    | zero => simpa only [iteratedDeriv_zero] using hf.decay.exp_mul c
    | succ j ih =>
        rw [iteratedDeriv_succ', deriv_exp_mul (hf.1.differentiable (by simp))]
        apply ih
        simpa only [Pi.add_def] using (hf.const_mul c).add hf.deriv

theorem SmoothSuperexponentialDecay.leftPrimitive {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hzero : ∫ x, f x = 0) :
    SmoothSuperexponentialDecay (RiemannResearch.Analysis.leftPrimitive f) := by
  have hi : Integrable f := by
    apply (hf.decay.integrable_weighted_norm hf.1.continuous (a := 0) le_rfl).mono'
      hf.1.continuous.aestronglyMeasurable
    exact ae_of_all _ (fun x => by simp)
  have hd := hasDerivAt_leftPrimitive hi hf.1.continuous
  have hderiv : _root_.deriv (RiemannResearch.Analysis.leftPrimitive f) = f :=
    funext (fun x => (hd x).deriv)
  constructor
  · apply contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞))
    intro j _
    cases j with
    | zero => simpa only [iteratedDeriv_zero] using
        (show Differentiable ℝ (RiemannResearch.Analysis.leftPrimitive f) from
          fun x => (hd x).differentiableAt)
    | succ j =>
        rw [iteratedDeriv_succ', hderiv]
        have hj : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j f) := by
          rw [iteratedDeriv_eq_iterate]
          exact ContDiff.iterate_deriv j hf.1
        exact hj.differentiable (by simp)
  · intro j
    cases j with
    | zero => simpa only [iteratedDeriv_zero] using
        hf.decay.leftPrimitive hf.1.continuous hzero
    | succ j => simpa only [iteratedDeriv_succ', hderiv] using hf.2 j

/-- The zero-removing integral stays inside the actual smooth test class used
by the complete arithmetic Weil formula. -/
theorem SmoothSuperexponentialDecay.removeTransformZero {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {z : ℂ}
    (hz : BilateralLaplace.centeredTransform f z = 0) :
    SmoothSuperexponentialDecay (removeTransformZero f z) := by
  let c : ℂ := z - 1 / 2
  let h : ℝ → ℂ := fun x => Complex.exp (-c * (x : ℂ)) * f x
  have hh : SmoothSuperexponentialDecay h := hf.exp_mul (-c)
  have hhzero : ∫ x, h x = 0 := by
    simpa only [BilateralLaplace.centeredTransform, BilateralLaplace.transform,
      BilateralLaplace.kernel, h, c, mul_comm] using hz
  exact (hh.leftPrimitive hhzero).exp_mul c

end
end RiemannResearch.Analysis
