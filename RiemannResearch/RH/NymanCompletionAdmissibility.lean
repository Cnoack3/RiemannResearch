import RiemannResearch.RH.NymanReturnRapidDecay
import RiemannResearch.Analysis.SmoothSuperexponentialDecay
import RiemannResearch.RH.ArithmeticCompletionDifferential
import RiemannResearch.RH.ArithmeticInverseCompact
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual differential-completion and remote-tail admissibility

The note's smooth test class requires every derivative to decrease faster
than every exponential. The statements below supply that class membership for
compact smooth seeds, the actual completed return, and its actual remote tail.
-/

namespace RiemannResearch.Analysis

/-- The concrete operator D²−1/4 preserves the full smooth decay class. -/
theorem SmoothSuperexponentialDecay.poleCancellationOperator {u : ℝ → ℂ}
    (hu : SmoothSuperexponentialDecay u) :
    SmoothSuperexponentialDecay (RiemannResearch.RH.poleCancellationOperator u) :=
  hu.deriv.deriv.sub (hu.const_smul (1 / 4))

end RiemannResearch.Analysis

namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- An explicit compact interval and actual smoothness supply rapid decay. -/
theorem superexponentialDecay_of_compact_interval {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) :
    SuperexponentialDecay u := by
  have hs : tsupport u ⊆ Set.Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro y hy
    constructor
    · by_contra h
      exact hy (ha y (lt_of_not_ge h))
    · by_contra h
      exact hy (hb y (lt_of_not_ge h))
  have hcs : HasCompactSupport u :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hs
  let f : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hu
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hC : 0 ≤ C := by positivity
  have hbound (y : ℝ) : ‖u y‖ ≤ C := by
    simpa [C, f] using SchwartzMap.norm_pow_mul_le_seminorm ℂ f 0 y
  intro d hd
  refine ⟨(C + 1) * Real.exp (d * (|a| + |b|)), by positivity, ?_⟩
  intro y
  by_cases hya : y < a
  · rw [ha y hya, norm_zero]
    positivity
  by_cases hyb : b < y
  · rw [hb y hyb, norm_zero]
    positivity
  have hy : |y| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor <;> nlinarith [le_of_not_gt hya, le_of_not_gt hyb,
      neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have hexp : 1 ≤ Real.exp (d * (|a| + |b|)) * Real.exp (-d * |y|) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by nlinarith)
  calc
    ‖u y‖ ≤ C := hbound y
    _ ≤ (C + 1) * (Real.exp (d * (|a| + |b|)) * Real.exp (-d * |y|)) := by
      nlinarith
    _ = _ := by ring

/-- Every derivative of a compact smooth seed is rapidly decreasing. -/
theorem smoothSuperexponentialDecay_of_compact_interval {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) :
    SmoothSuperexponentialDecay u := by
  refine ⟨hu, ?_⟩
  intro j
  have hj : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j u) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv j hu
  exact superexponentialDecay_of_compact_interval hj
    (iteratedDeriv_zero_below_of_zero_below ha j)
    (iteratedDeriv_zero_above_of_zero_above hb j)

theorem smoothSuperexponentialDecay_nymanFullReturn {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    (n : ℕ) [NeZero n] : SmoothSuperexponentialDecay (nymanFullReturn n u) :=
  nymanFullReturn_smooth_and_all_derivatives_decay hu ha hb n

/-- The actual completed test belongs to E, with all derivative bounds proved. -/
theorem smoothSuperexponentialDecay_nymanCompletedTest (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    SmoothSuperexponentialDecay (nymanCompletedTest n M hn v) := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)⟩
  apply SmoothSuperexponentialDecay.poleCancellationOperator
  exact smoothSuperexponentialDecay_nymanFullReturn
    (nymanInversePotential_contDiff n M hn hv)
    (fun x hx => nymanInversePotential_zero_below n M hn ha hx)
    (fun x hx => nymanInversePotential_zero_above n M hn hb hx) n

/-- The actual remote tail belongs to E; no tail decay is assumed. -/
theorem smoothSuperexponentialDecay_nymanCompletionTail (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    SmoothSuperexponentialDecay (nymanCompletionTail n M hn v) :=
  (smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb).sub
    (smoothSuperexponentialDecay_of_compact_interval hv ha hb).poleCancellationOperator

/-- The complete support and regularity conclusion for the actual remote tail. -/
theorem nymanCompletionTail_admissible_and_tsupport (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    SmoothSuperexponentialDecay (nymanCompletionTail n M hn v) ∧
      tsupport (nymanCompletionTail n M hn v) ⊆
        Set.Ici (a + Real.log (M + 1 : ℕ)) :=
  ⟨smoothSuperexponentialDecay_nymanCompletionTail n M hn hv ha hb,
    nymanCompletionTail_tsupport n M hn ha⟩

end RiemannResearch.RH
