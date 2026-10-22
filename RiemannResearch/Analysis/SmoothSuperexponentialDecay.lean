import RiemannResearch.Analysis.SuperexponentialDecay
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth superexponential decay and its elementary closure properties

Source: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. These declarations are moved verbatim from
`RH/NymanCompletionAdmissibility`; the arithmetic completion applications
remain in that module.
-/

namespace RiemannResearch.Analysis

/-- The smooth superexponential class E used by the Nyman--Weil construction. -/
def SmoothSuperexponentialDecay (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧
    ∀ j : ℕ, SuperexponentialDecay (iteratedDeriv j f)

theorem SuperexponentialDecay.sub {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g) :
    SuperexponentialDecay (f - g) := by
  intro a ha
  obtain ⟨C, hC, hCf⟩ := hf a ha
  obtain ⟨D, hD, hDg⟩ := hg a ha
  refine ⟨C + D, by positivity, ?_⟩
  intro y
  exact (norm_sub_le _ _).trans (by
    change ‖f y‖ + ‖g y‖ ≤ (C + D) * Real.exp (-a * |y|)
    nlinarith [hCf y, hDg y])

theorem SuperexponentialDecay.const_smul {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (c : ℝ) :
    SuperexponentialDecay (c • f) := by
  intro a ha
  obtain ⟨C, hC, hCf⟩ := hf a ha
  refine ⟨(‖c‖ + 1) * C, by positivity, ?_⟩
  intro y
  change ‖c • f y‖ ≤ _
  rw [norm_smul]
  calc
    ‖c‖ * ‖f y‖ ≤ ‖c‖ * (C * Real.exp (-a * |y|)) :=
      mul_le_mul_of_nonneg_left (hCf y) (norm_nonneg _)
    _ ≤ _ := by nlinarith [Real.exp_pos (-a * |y|), norm_nonneg c]

theorem SmoothSuperexponentialDecay.decay {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) : SuperexponentialDecay f := by
  simpa only [iteratedDeriv_zero] using hf.2 0

theorem SmoothSuperexponentialDecay.deriv {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) : SmoothSuperexponentialDecay (deriv f) := by
  constructor
  · simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hf.1
  · intro j
    simpa only [iteratedDeriv_succ'] using hf.2 (j + 1)

theorem SmoothSuperexponentialDecay.sub {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) :
    SmoothSuperexponentialDecay (f - g) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  intro j
  have hj : (j : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le
  have he : iteratedDeriv j (f - g) = iteratedDeriv j f - iteratedDeriv j g := by
    funext x
    exact iteratedDeriv_sub ((hf.1.of_le hj).contDiffAt) ((hg.1.of_le hj).contDiffAt)
  rw [he]
  exact (hf.2 j).sub (hg.2 j)

theorem SmoothSuperexponentialDecay.const_smul {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (c : ℝ) :
    SmoothSuperexponentialDecay (c • f) := by
  refine ⟨(contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : ℝ => c)).smul hf.1, ?_⟩
  intro j
  have he : iteratedDeriv j (c • f) = c • iteratedDeriv j f := by
    funext x
    exact iteratedDeriv_const_smul_field c f
  rw [he]
  exact (hf.2 j).const_smul c

end RiemannResearch.Analysis
